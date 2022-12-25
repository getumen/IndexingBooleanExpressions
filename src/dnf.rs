use anyhow::{anyhow, Result};
use min_max_heap::MinMaxHeap;
use std::{
    cmp::{self, Ordering},
    collections::HashMap,
};

use crate::{BooleanExpression, BooleanFeature, Document, Term};

#[derive(Debug)]
struct Posting {
    doc_id: u64,
    is_in: bool,
}

impl PartialEq for Posting {
    fn eq(&self, other: &Self) -> bool {
        self.doc_id == other.doc_id
    }
}

impl Eq for Posting {}

impl PartialOrd for Posting {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Posting {
    fn cmp(&self, other: &Self) -> Ordering {
        self.doc_id.cmp(&other.doc_id)
    }
}

impl Posting {
    fn new(doc_id: u64, is_in: bool) -> Self {
        Posting { doc_id, is_in }
    }
}

#[derive(Debug)]
struct PostingList {
    value: Vec<Posting>,
}

impl PostingList {
    fn new() -> Self {
        PostingList { value: Vec::new() }
    }

    fn merge(&mut self, posting: Posting) {
        match self.value.binary_search(&posting) {
            Ok(i) => {
                if self.value[i].is_in == !posting.is_in {
                    panic!("常に偽になるドキュメント")
                }
            }
            Err(i) => self.value.insert(i, posting),
        }
    }

    fn cursor(&self) -> PostingListCursor {
        PostingListCursor {
            value: &self.value,
            cursor: 0,
        }
    }
}

#[derive(Debug)]
struct PostingListCursor<'a> {
    value: &'a Vec<Posting>,
    cursor: usize,
}

impl<'a> PostingListCursor<'a> {
    fn new(value: &'a Vec<Posting>) -> Self {
        PostingListCursor { value, cursor: 0 }
    }

    fn current(&self) -> &Posting {
        &self.value[self.cursor]
    }

    fn valid(&self) -> bool {
        self.cursor < self.value.len()
    }

    fn next(&mut self) {
        self.cursor += 1;
    }

    fn seek(&mut self, doc_id: u64) -> Option<&Posting> {
        match self.value.as_slice()[self.cursor..].binary_search(&Posting {
            doc_id,
            is_in: true,
        }) {
            Ok(i) => {
                self.cursor += i;
                Some(&self.value[self.cursor])
            }
            Err(i) => {
                self.cursor += i;
                None
            }
        }
    }
}

// heap用に実装
impl<'a> PartialEq for PostingListCursor<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.current().doc_id == other.current().doc_id
            && self.current().is_in == other.current().is_in
    }
}
// heap用に実装
impl<'a> Eq for PostingListCursor<'a> {}

impl<'a> PartialOrd for PostingListCursor<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// heap用に実装
impl<'a> Ord for PostingListCursor<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.current().doc_id.cmp(&other.current().doc_id) {
            Ordering::Equal => self.current().is_in.cmp(&other.current().is_in),
            ord => return ord,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Index {
    k_index: Vec<HashMap<Term, PostingList>>,
}

impl Index {
    pub fn new() -> Self {
        Index {
            k_index: Vec::new(),
        }
    }

    pub fn add_doc(&mut self, doc: &Document) -> Result<()> {
        if doc.boolean_expression.or.len() > 0 {
            return Err(anyhow!("not DNF"));
        }

        let k = count_conjunctions_size(&doc.boolean_expression.and);
        for _ in self.k_index.len()..(k + 1) {
            self.k_index.push(HashMap::new());
        }

        for c in &doc.boolean_expression.and {
            add_feature(&mut self.k_index, k, doc.doc_id, c, true);
        }

        if k == 0 {
            add_feature(
                &mut self.k_index,
                k,
                doc.doc_id,
                &BooleanExpression::new(BooleanFeature::Empty),
                true,
            )
        }

        Ok(())
    }

    pub fn search(&self, assignments: &Vec<Term>) -> Result<Vec<u64>> {
        let mut result = Vec::new();

        for k in (0..cmp::min(self.k_index.len(), assignments.len() + 1)).rev() {
            let mut postings = Vec::new();
            for assignment in assignments {
                match self.k_index[k].get(assignment) {
                    Some(pl) => postings.push(pl),
                    None => {}
                }
            }
            let k = if k == 0 { 1 } else { k };
            if postings.len() < k {
                continue;
            }

            let mut posting_list_heap = MinMaxHeap::new();
            for v in &postings {
                let it = v.cursor();
                posting_list_heap.push(it);
            }

            while posting_list_heap.len() > 0 {
                let max_posting_doc_id = posting_list_heap.peek_max().unwrap().current().doc_id;
                let mut min_posting_cur = posting_list_heap.pop_min().unwrap();

                let min_posting = min_posting_cur.current();

                if min_posting.doc_id == max_posting_doc_id {
                    if min_posting.is_in {
                        result.push(min_posting.doc_id);
                    }

                    // ドキュメントが見つかったら、heap内のカーソルを全て次に移動
                    loop {
                        if min_posting_cur.current().doc_id == max_posting_doc_id {
                            min_posting_cur.next();
                            if min_posting_cur.valid() {
                                posting_list_heap.push(min_posting_cur);
                            }
                            if posting_list_heap.len() == 0 {
                                break;
                            }
                            min_posting_cur = posting_list_heap.pop_min().unwrap();
                        } else {
                            posting_list_heap.push(min_posting_cur);
                            break;
                        }
                    }
                } else {
                    // 見つからなかったら、一番小さいカーソルを最大のdoc_idに移動
                    min_posting_cur.seek(max_posting_doc_id);
                    if min_posting_cur.valid() {
                        posting_list_heap.push(min_posting_cur);
                    }
                }
            }
        }
        Ok(result)
    }
}

fn count_conjunctions_size(v: &Vec<BooleanExpression>) -> usize {
    let mut k = 0;
    for x in v {
        match x.feature {
            Some(_) => k += 1,
            None => {}
        }
    }
    k
}

fn add_feature(
    k_index: &mut Vec<HashMap<Term, PostingList>>,
    k: usize,
    doc_id: u64,
    boolean_expression: &BooleanExpression,
    is_in: bool,
) {
    if let Some(f) = &boolean_expression.feature {
        for cond in f.conditions() {
            let posting_list: Option<&mut PostingList> = k_index[k].get_mut(&cond);
            if let Some(pl) = posting_list {
                pl.merge(Posting::new(doc_id, is_in))
            } else {
                let mut pl = PostingList::new();
                pl.merge(Posting::new(doc_id, is_in));
                k_index[k].insert(cond, pl);
            }
        }
    } else {
        add_feature(
            k_index,
            k,
            doc_id,
            boolean_expression
                .not
                .as_ref()
                .expect("in, not_inのどちらでもない不正な条件式"),
            !is_in,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn posting_order_doc_id() {
        assert_eq!(
            Posting {
                doc_id: 1,
                is_in: true
            } < Posting {
                doc_id: 2,
                is_in: false
            },
            true,
        );
    }

    #[test]
    fn posting_order_eq() {
        assert_eq!(
            Posting {
                doc_id: 1,
                is_in: true
            } == Posting {
                doc_id: 1,
                is_in: false
            },
            true,
        );
    }

    #[test]
    fn posting_list_cursor_ord() {
        assert!(
            PostingListCursor::new(&vec![Posting::new(1, false)])
                < PostingListCursor::new(&vec![Posting::new(1, true)])
        )
    }

    #[test]
    fn posting_list_cursor_seek() {
        assert_eq!(
            PostingListCursor::new(&vec![
                Posting::new(1, false),
                Posting::new(3, false),
                Posting::new(5, false),
            ])
            .seek(3),
            Some(&Posting::new(3, false)),
        );

        assert_eq!(
            PostingListCursor::new(&vec![
                Posting::new(1, false),
                Posting::new(3, false),
                Posting::new(5, false),
            ])
            .seek(4),
            None,
        );
    }
}
