// https://theory.stanford.edu/~sergei/papers/vldb09-indexing.pdf

use std::{cmp::Ordering, collections::HashMap};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::fmt::Debug;
use std::hash::Hash;

use crate::boolean_expression::{self, BooleanExpression};

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Term<T: Debug + Clone + PartialEq + PartialOrd + Eq + Ord + Hash> {
    Empty,
    Some(T),
}

#[derive(Debug, Clone)]
struct Posting {
    doc_id: u32,
    conj_id: u32,
    is_not: bool,
    impact_score_factor: f32,
}

impl Posting {
    fn new(doc_id: u32, conj_id: u32, is_not: bool, impact_score_factor: f32) -> Self {
        Self {
            doc_id,
            conj_id,
            is_not,
            impact_score_factor,
        }
    }
}

impl PartialEq for Posting {
    fn eq(&self, other: &Self) -> bool {
        self.doc_id == other.doc_id && self.conj_id == other.conj_id
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
        match self.doc_id.cmp(&other.doc_id) {
            Ordering::Equal => self.conj_id.cmp(&other.conj_id),
            ord @ _ => ord,
        }
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
            Ok(_) => {}
            Err(i) => self.value.insert(i, posting),
        }
    }

    fn cursor(&self) -> PostingListCursor {
        PostingListCursor::new(&self.value)
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

    fn value(&self) -> &Posting {
        &self.value[self.cursor]
    }

    fn next(&mut self) -> bool {
        self.cursor += 1;
        self.cursor < self.value.len()
    }

    fn next_doc(&mut self) -> bool {
        self.skip(&Posting::new(self.value().doc_id + 1, 0, false, 1f32))
    }

    fn skip(&mut self, posting: &Posting) -> bool {
        match self.value.as_slice()[self.cursor..].binary_search(posting) {
            Ok(i) => {
                self.cursor += i;
                self.cursor < self.value.len()
            }
            Err(i) => {
                self.cursor += i;
                self.cursor < self.value.len()
            }
        }
    }
}

// heap用に実装
impl<'a> PartialEq for PostingListCursor<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value() && self.value().is_not == other.value().is_not
    }
}

impl<'a> Eq for PostingListCursor<'a> {}

impl<'a> PartialOrd for PostingListCursor<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> Ord for PostingListCursor<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.value().cmp(&other.value()) {
            // notが小さくなるようにする
            Ordering::Equal => (self.value().is_not).cmp(&other.value().is_not).reverse(),
            ord => ord,
        }
    }
}

#[derive(Debug)]
pub struct Index<T: Debug + Clone + PartialEq + PartialOrd + Eq + Ord + Hash> {
    k_index: Vec<HashMap<Term<T>, PostingList>>,
}

impl<T: Debug + Clone + PartialEq + PartialOrd + Eq + Ord + Hash> Index<T> {
    pub fn new() -> Self {
        Index {
            k_index: Vec::new(),
        }
    }

    pub fn add_doc(
        &mut self,
        doc_id: u32,
        be: BooleanExpression<Term<T>>,
        impact_factors: &HashMap<Term<T>, f32>,
    ) -> Result<()> {
        let be = boolean_expression::simplify(boolean_expression::to_dnf(be));
        match be {
            BooleanExpression::Disjunction(v) => {
                // conj_idをconj impact factorに降順になるように振る

                let mut v: Vec<(BooleanExpression<Term<T>>, f32)> = v
                    .into_iter()
                    .flat_map(|x| {
                        Self::decompose_conjunction_by_impact_factor(x, impact_factors).unwrap()
                    })
                    .collect();

                v.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap().reverse());

                for (conj_id, (conj, conj_score)) in v.into_iter().enumerate() {
                    self.add_conj(doc_id, conj_id as u32, conj_score, conj)?;
                }
                Ok(())
            }
            _ => {
                Self::decompose_conjunction_by_impact_factor(be, impact_factors)?
                    .into_iter()
                    .for_each(|(expr, score)| self.add_conj(doc_id, 0, score, expr).unwrap());
                Ok(())
            }
        }
    }

    fn decompose_conjunction_by_impact_factor(
        be: BooleanExpression<Term<T>>, // conjunction
        impact_factors: &HashMap<Term<T>, f32>,
    ) -> Result<Vec<(BooleanExpression<Term<T>>, f32)>> {
        match be {
            BooleanExpression::True => Ok(vec![(be, 1.)]),
            BooleanExpression::False => Ok(vec![(be, 0.)]),
            BooleanExpression::Contain(v) => Ok(v
                .into_iter()
                .group_by(|x| *impact_factors.get(x).unwrap_or(&1f32))
                .into_iter()
                .map(|(factor, exprs)| {
                    (
                        BooleanExpression::Contain(exprs.collect::<Vec<Term<T>>>()),
                        factor,
                    )
                })
                .collect()),
            BooleanExpression::Negation(box BooleanExpression::Contain(v)) => Ok(v
                .into_iter()
                .group_by(|x| *impact_factors.get(x).unwrap_or(&1f32))
                .into_iter()
                .map(|(factor, exprs)| {
                    (
                        BooleanExpression::Negation(Box::new(BooleanExpression::Contain(
                            exprs.collect::<Vec<Term<T>>>(),
                        ))),
                        factor,
                    )
                })
                .collect()),
            BooleanExpression::Conjunction(expr) => Ok(expr
                .into_iter()
                .map(|x| Self::decompose_conjunction_by_impact_factor(x, impact_factors).unwrap())
                .multi_cartesian_product()
                .map(|x| {
                    let mut exprs = Vec::new();
                    let mut factor = 1f32;
                    for (expr, f) in x {
                        exprs.push(expr);
                        factor *= f;
                    }
                    (BooleanExpression::Conjunction(exprs), factor)
                })
                .collect()),
            _ => Err(anyhow!("DNFではない")),
        }
    }

    fn add_conj(
        &mut self,
        doc_id: u32,
        conj_id: u32,
        conj_score: f32,
        be: BooleanExpression<Term<T>>,
    ) -> Result<()> {
        let k = match &be {
            BooleanExpression::Conjunction(v) => v
                .iter()
                .filter_map(|x| match x {
                    BooleanExpression::Contain(_) => Some(x),
                    _ => None,
                })
                .count(),
            BooleanExpression::True => 0,
            BooleanExpression::False => return Ok(()),
            BooleanExpression::Contain(_) => 1,
            BooleanExpression::Negation(_) => 0,
            _ => return Err(anyhow!("DNFではない")),
        };

        // k_indexが現在保持しているものより少なかったら、拡張する
        for _ in self.k_index.len()..(k + 1) {
            self.k_index.push(HashMap::new());
        }

        match &be {
            BooleanExpression::Conjunction(v) => {
                for e in v {
                    match e {
                        BooleanExpression::Contain(v) => {
                            self.add_feature(k, doc_id, conj_id, conj_score, v, false)
                        }
                        BooleanExpression::Negation(box BooleanExpression::Contain(t)) => {
                            self.add_feature(k, doc_id, conj_id, conj_score, t, true)
                        }
                        _ => Err(anyhow!("DNFではない")),
                    }?;
                }
            }
            BooleanExpression::Contain(v) => {
                self.add_feature(k, doc_id, conj_id, conj_score, v, false)?
            }
            BooleanExpression::Negation(box BooleanExpression::Contain(v)) => {
                self.add_feature(k, doc_id, conj_id, conj_score, v, true)?
            }
            BooleanExpression::True => {
                // Term::Emptyだけ登録すれば良い
            }
            _ => return Err(anyhow!("DNFではない")),
        };

        if k == 0 {
            self.add_feature(k, doc_id, conj_id, 1., &vec![Term::Empty], false)?;
        }
        Ok(())
    }

    fn add_feature(
        &mut self,
        k: usize,
        doc_id: u32,
        conj_id: u32,
        conj_score: f32,
        terms: &[Term<T>],
        is_not: bool,
    ) -> Result<()> {
        for term in terms {
            let posting_list: Option<&mut PostingList> = self.k_index[k].get_mut(term);
            if let Some(pl) = posting_list {
                pl.merge(Posting::new(doc_id, conj_id, is_not, conj_score));
            } else {
                let mut pl = PostingList::new();
                pl.merge(Posting::new(doc_id, conj_id, is_not, conj_score));
                self.k_index[k].insert(term.clone(), pl);
            }
        }

        Ok(())
    }

    fn union_search_result(left: Vec<(u32, f32)>, right: Vec<(u32, f32)>) -> Vec<(u32, f32)> {
        let mut left_cur = 0;
        let mut right_cur = 0;
        let mut result = Vec::new();
        while left_cur < left.len() && right_cur < right.len() {
            match left[left_cur].0.cmp(&right[right_cur].0) {
                Ordering::Less => {
                    result.push(left[left_cur]);
                    left_cur += 1;
                }
                Ordering::Equal => {
                    if left[left_cur].1 > right[right_cur].1 {
                        result.push(left[left_cur]);
                    } else {
                        result.push(right[right_cur]);
                    }

                    left_cur += 1;
                    right_cur += 1;
                }
                Ordering::Greater => {
                    result.push(right[right_cur]);
                    right_cur += 1;
                }
            }
        }

        for i in left_cur..left.len() {
            result.push(left[i]);
        }

        for i in right_cur..right.len() {
            result.push(right[i]);
        }

        result
    }

    pub fn search(&self, assignments: &Vec<Term<T>>) -> Result<Vec<(u32, f32)>> {
        let mut result = Vec::new();

        for k in (0..std::cmp::min(self.k_index.len(), assignments.len() + 1)).rev() {
            result = Self::union_search_result(result, self.search_in_k(assignments, k)?);
        }
        Ok(result)
    }

    fn search_in_k(&self, assignments: &Vec<Term<T>>, k: usize) -> Result<Vec<(u32, f32)>> {
        let mut result = Vec::new();
        let mut postings = Vec::new();
        for assignment in assignments {
            match self.k_index[k].get(assignment) {
                Some(pl) => postings.push(pl),
                None => {}
            }
        }
        if k == 0 {
            match self.k_index[k].get(&Term::Empty) {
                Some(pl) => postings.push(pl),
                None => {}
            }
        }
        let k = if k == 0 { 1 } else { k };
        if postings.len() < k {
            return Ok(Vec::new());
        }
        let mut posting_lists = Vec::new();
        for v in &postings {
            let it = v.cursor();
            posting_lists.push(it);
        }

        while posting_lists.len() >= k {
            posting_lists.sort();

            let mut removable_index = Vec::new();
            if posting_lists[0].value() == posting_lists[k - 1].value() {
                // 最も小さいポスティングがNOTならばそのdoc_id*conj_idは読み飛ばせる
                // next()に注意
                if posting_lists[0].value().is_not {
                    let max_same_posing_count = posting_lists
                        .iter()
                        .filter(|x| x.value() == posting_lists[0].value())
                        .count();
                    for i in 0..max_same_posing_count {
                        if !posting_lists[i].next() {
                            removable_index.push(i);
                        }
                    }
                    for i in removable_index.iter().rev() {
                        posting_lists.remove(*i);
                    }
                    continue;
                }

                result.push((
                    posting_lists[0].value().doc_id,
                    posting_lists[0].value().impact_score_factor,
                ));

                let max_same_posing_count = posting_lists
                    .iter()
                    .filter(|x| x.value() == posting_lists[0].value())
                    .count();
                for i in 0..max_same_posing_count {
                    // next_doc()に注意
                    if !posting_lists[i].next_doc() {
                        removable_index.push(i);
                    }
                }
                for i in removable_index.iter().rev() {
                    posting_lists.remove(*i);
                }
            } else {
                let last_posting = posting_lists[k - 1].value().clone();

                // 見つからなかったら、0..(k-2)のカーソルを(k-1)のdoc_idに移動
                for i in 0..(k - 1) {
                    // next_doc()に注意
                    if !posting_lists[i].skip(&last_posting) {
                        removable_index.push(i);
                    }
                }
                for i in removable_index.iter().rev() {
                    posting_lists.remove(*i);
                }
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn posting_ord() {
        assert_eq!(
            Posting::new(1, 0, true, 1.) < Posting::new(1, 1, false, 1.),
            true
        );
        assert_eq!(
            Posting::new(1, 0, true, 1.) == Posting::new(1, 0, false, 1.),
            true
        );
        assert_eq!(
            Posting::new(1, 0, true, 1.) > Posting::new(1, 0, false, 1.),
            false,
        );
    }

    #[test]
    fn posting_list_cursor_ord() {
        assert_eq!(
            PostingListCursor::new(&vec![Posting::new(1, 0, true, 1.),])
                < PostingListCursor::new(&vec![Posting::new(1, 0, false, 1.),]),
            true,
        );
        assert_eq!(
            PostingListCursor::new(&vec![Posting::new(1, 0, true, 1.),])
                == PostingListCursor::new(&vec![Posting::new(1, 0, false, 1.),]),
            false,
        );
        assert_eq!(
            PostingListCursor::new(&vec![Posting::new(1, 0, true, 1.),])
                > PostingListCursor::new(&vec![Posting::new(1, 0, false, 1.),]),
            false,
        );
    }

    #[test]
    fn decompose_conjunction_by_impact_factor() {
        let mut impact_factor = HashMap::new();
        impact_factor.insert(Term::Some("area:1"), 0.5);

        assert_eq!(
            Index::decompose_conjunction_by_impact_factor(
                BooleanExpression::Conjunction(vec![
                    BooleanExpression::Contain(vec![Term::Some("area:1"), Term::Some("area:2"),]),
                    BooleanExpression::Contain(vec![
                        Term::Some("gender:1"),
                        Term::Some("gender:2"),
                    ])
                ]),
                &impact_factor,
            )
            .unwrap(),
            vec![
                (
                    BooleanExpression::Conjunction(vec![
                        BooleanExpression::Contain(vec![Term::Some("area:1"),]),
                        BooleanExpression::Contain(vec![
                            Term::Some("gender:1"),
                            Term::Some("gender:2"),
                        ])
                    ]),
                    0.5f32,
                ),
                (
                    BooleanExpression::Conjunction(vec![
                        BooleanExpression::Contain(vec![Term::Some("area:2"),]),
                        BooleanExpression::Contain(vec![
                            Term::Some("gender:1"),
                            Term::Some("gender:2"),
                        ])
                    ]),
                    1f32,
                )
            ]
        );
    }

    #[test]
    fn integration_test() {
        let mut target = Index::new();

        let mut impact_factor = HashMap::new();

        impact_factor.insert(Term::Some("area:1"), 0.5);

        target
            .add_doc(
                1,
                BooleanExpression::Contain(vec![
                    Term::Some("area:1"),
                    Term::Some("area:2"),
                    Term::Some("area:3"),
                ]),
                &impact_factor,
            )
            .unwrap();

        target
            .add_doc(
                3,
                (BooleanExpression::Contain(vec![Term::Some("gender:1")])
                    | (BooleanExpression::Contain(vec![Term::Some("gender:2")])
                        & BooleanExpression::Contain(vec![Term::Some("age:1")])))
                    & (BooleanExpression::Contain(vec![
                        Term::Some("area:1"),
                        Term::Some("area:2"),
                        Term::Some("area:3"),
                    ]) | (BooleanExpression::Contain(vec![Term::Some("device:1")])
                        & !BooleanExpression::Contain(vec![Term::Some("device:2")]))),
                &impact_factor,
            )
            .unwrap();

        target
            .add_doc(5, BooleanExpression::True, &impact_factor)
            .unwrap();
        target
            .add_doc(7, BooleanExpression::False, &impact_factor)
            .unwrap();

        assert_eq!(
            target.search(&vec![Term::Some("area:1")]).unwrap(),
            vec![(1, 0.5f32), (5, 1f32)]
        );

        assert_eq!(
            target
                .search(&vec![
                    Term::Some("gender:2"),
                    Term::Some("age:1"),
                    Term::Some("device:1"),
                ])
                .unwrap(),
            vec![(3, 1f32), (5, 1f32)]
        );

        // 除外を入れる
        assert_eq!(
            target
                .search(&vec![
                    Term::Some("gender:2"),
                    Term::Some("age:1"),
                    Term::Some("device:1"),
                    Term::Some("device:2"),
                ])
                .unwrap(),
            vec![(5, 1f32)]
        );

        // 年齢が足りない
        assert_eq!(
            target
                .search(&vec![Term::Some("gender:2"), Term::Some("device:1"),])
                .unwrap(),
            vec![(5, 1f32)]
        );
    }
}
