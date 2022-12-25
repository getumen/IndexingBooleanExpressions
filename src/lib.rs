pub mod dnf;

struct BooleanExpression {
    and: Vec<BooleanExpression>,
    or: Vec<BooleanExpression>,
    not: Option<Box<BooleanExpression>>,
    feature: Option<BooleanFeature>,
}

impl BooleanExpression {
    fn new_and(expressions: Vec<BooleanExpression>) -> Self {
        // TODO: 常に偽になる条件式がないかチェック
        BooleanExpression {
            and: expressions,
            or: Vec::new(),
            not: None,
            feature: None,
        }
    }

    fn new_or(expressions: Vec<BooleanExpression>) -> Self {
        // TODO: 常に真になる条件式を除く
        BooleanExpression {
            and: Vec::new(),
            or: expressions,
            not: None,
            feature: None,
        }
    }

    fn new_not(expression: BooleanExpression) -> Self {
        BooleanExpression {
            and: Vec::new(),
            or: Vec::new(),
            not: Some(Box::new(expression)),
            feature: None,
        }
    }

    fn new(expression: BooleanFeature) -> Self {
        BooleanExpression {
            and: Vec::new(),
            or: Vec::new(),
            not: None,
            feature: Some(expression),
        }
    }
}

enum BooleanFeature {
    Feature { column: String, values: Vec<String> },
    Empty,
}

impl BooleanFeature {
    fn new(column: String, values: Vec<String>) -> Self {
        BooleanFeature::Feature { column, values }
    }

    fn conditions(&self) -> Vec<Term> {
        let mut v = Vec::new();
        match &self {
            Self::Feature { column, values } => {
                for x in values {
                    v.push(Term::new(column.clone(), x.clone()));
                }
            }
            Self::Empty => v.push(Term::Empty),
        }

        v
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
enum Term {
    Condition { key: String, value: String },
    Empty,
}

impl Term {
    fn new(key: String, value: String) -> Self {
        Term::Condition { key, value }
    }

    fn empty() -> Self {
        Term::Empty
    }
}

struct Document {
    doc_id: u64,
    boolean_expression: BooleanExpression,
}

impl Document {
    fn new(doc_id: u64, boolean_expression: BooleanExpression) -> Self {
        Document {
            doc_id,
            boolean_expression,
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dnf_search() {
        let mut dnf_index = dnf::Index::new();
        dnf_index
            .add_doc(&Document::new(
                1,
                BooleanExpression::new_and(vec![
                    BooleanExpression::new(BooleanFeature::new(
                        "age".to_string(),
                        vec!["3".to_string()],
                    )),
                    BooleanExpression::new(BooleanFeature::new(
                        "state".to_string(),
                        vec!["NY".to_string()],
                    )),
                ]),
            ))
            .unwrap();
        dnf_index
            .add_doc(&Document::new(
                2,
                BooleanExpression::new_and(vec![
                    BooleanExpression::new(BooleanFeature::new(
                        "age".to_string(),
                        vec!["3".to_string()],
                    )),
                    BooleanExpression::new(BooleanFeature::new(
                        "gender".to_string(),
                        vec!["F".to_string()],
                    )),
                ]),
            ))
            .unwrap();

        dnf_index
            .add_doc(&Document::new(
                3,
                BooleanExpression::new_and(vec![
                    BooleanExpression::new(BooleanFeature::new(
                        "age".to_string(),
                        vec!["3".to_string()],
                    )),
                    BooleanExpression::new(BooleanFeature::new(
                        "gender".to_string(),
                        vec!["M".to_string()],
                    )),
                    BooleanExpression::new_not(BooleanExpression::new(BooleanFeature::new(
                        "state".to_string(),
                        vec!["CA".to_string()],
                    ))),
                ]),
            ))
            .unwrap();

        dnf_index
            .add_doc(&Document::new(
                4,
                BooleanExpression::new_and(vec![
                    BooleanExpression::new(BooleanFeature::new(
                        "state".to_string(),
                        vec!["CA".to_string()],
                    )),
                    BooleanExpression::new(BooleanFeature::new(
                        "gender".to_string(),
                        vec!["M".to_string()],
                    )),
                ]),
            ))
            .unwrap();

        dnf_index
            .add_doc(&Document::new(
                5,
                BooleanExpression::new_and(vec![BooleanExpression::new(BooleanFeature::new(
                    "age".to_string(),
                    vec!["3".to_string(), "4".to_string()],
                ))]),
            ))
            .unwrap();

        dnf_index
            .add_doc(&Document::new(
                6,
                BooleanExpression::new_and(vec![BooleanExpression::new_not(
                    BooleanExpression::new(BooleanFeature::new(
                        "state".to_string(),
                        vec!["CA".to_string(), "NY".to_string()],
                    )),
                )]),
            ))
            .unwrap();

        assert_eq!(
            dnf_index
                .search(&vec![
                    Term::new("age".to_string(), "3".to_string()),
                    Term::new("state".to_string(), "CA".to_string()),
                    Term::new("gender".to_string(), "M".to_string()),
                ])
                .unwrap(),
            vec![4, 5]
        );

        assert_eq!(dnf_index.search(&vec![Term::Empty]).unwrap(), vec![6]);
    }
}
