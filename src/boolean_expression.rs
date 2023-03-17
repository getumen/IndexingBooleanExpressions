use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{BitAnd, BitOr, Not};

// ref. https://hackage.haskell.org/package/hatt-1.5.0.3/docs/src/Data-Logic-Propositional-NormalForms.html
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum BooleanExpression<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash> {
    True,
    False,
    Contain(Vec<T>),
    Negation(Box<BooleanExpression<T>>),
    Conjunction(Vec<BooleanExpression<T>>),
    Disjunction(Vec<BooleanExpression<T>>),
}

impl<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash> Debug for BooleanExpression<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conjunction(v) => {
                write!(
                    f,
                    "({})",
                    v.iter()
                        .map(|x| format!("{:?}", x))
                        .collect::<Vec<String>>()
                        .join(" & ")
                )
            }
            Self::Disjunction(v) => write!(
                f,
                "({})",
                v.iter()
                    .map(|x| format!("{:?}", x))
                    .collect::<Vec<String>>()
                    .join(" | ")
            ),
            Self::Negation(a) => write!(f, "!{:?}", a),
            Self::Contain(a) => write!(f, "Contain{:?}", a),
            Self::True => f.debug_struct("True").finish(),
            Self::False => f.debug_struct("False").finish(),
        }
    }
}

impl<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash> BitAnd<BooleanExpression<T>>
    for BooleanExpression<T>
{
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::Conjunction(vec![self.clone(), rhs.clone()])
    }
}

impl<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash> BitOr<BooleanExpression<T>>
    for BooleanExpression<T>
{
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::Disjunction(vec![self.clone(), rhs.clone()])
    }
}

impl<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash> Not for BooleanExpression<T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            BooleanExpression::Negation(box a) => a.clone(),
            _ => BooleanExpression::Negation(Box::new(self.clone())),
        }
    }
}

pub fn to_nnf<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    be: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match be {
        BooleanExpression::Negation(box a) => match a {
            BooleanExpression::Negation(box expr) => expr,
            BooleanExpression::Conjunction(v) => {
                BooleanExpression::Disjunction(v.into_iter().map(|x| to_nnf(!x)).collect())
            }
            BooleanExpression::Disjunction(v) => {
                BooleanExpression::Conjunction(v.into_iter().map(|x| to_nnf(!x)).collect())
            }
            operand @ _ => !operand,
        },
        BooleanExpression::Conjunction(v) => {
            BooleanExpression::Conjunction(v.into_iter().map(to_nnf).collect())
        }
        BooleanExpression::Disjunction(v) => {
            BooleanExpression::Disjunction(v.into_iter().map(to_nnf).collect())
        }
        _ => be.clone(),
    }
}

pub fn to_cnf<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    be: BooleanExpression<T>,
) -> BooleanExpression<T> {
    make_cnf(to_nnf(be))
}

fn make_cnf<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    be: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match be {
        BooleanExpression::Conjunction(v) => flatten(BooleanExpression::Conjunction(
            v.into_iter().map(make_cnf).collect(),
        )),
        BooleanExpression::Disjunction(v) => {
            let e = v
                .into_iter()
                .map(make_cnf)
                .collect::<Vec<BooleanExpression<T>>>();
            flatten(BooleanExpression::Conjunction(
                distribute_conjunctions::<T>(&e),
            ))
        }
        _ => be.clone(),
    }
}

fn distribute_conjunctions<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    v: &Vec<BooleanExpression<T>>,
) -> Vec<BooleanExpression<T>> {
    fn go<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
        out: &mut Vec<BooleanExpression<T>>,
        with: &mut Vec<BooleanExpression<T>>,
        rest: &[BooleanExpression<T>],
    ) {
        match rest {
            [head, tail @ ..] => match head {
                BooleanExpression::Conjunction(disj) => {
                    for part in disj {
                        with.push(part.clone());
                        go(out, with, tail);
                        with.pop();
                    }
                }
                _ => {
                    with.push(head.clone());
                    go(out, with, tail);
                    with.pop();
                }
            },
            _ => {
                // Turn accumulated parts into a new conjunction.
                out.push(BooleanExpression::Disjunction(with.clone()));
            }
        }
    }

    let mut out = Vec::new(); // contains only `all()`
    let mut with = Vec::new();

    go(&mut out, &mut with, v);

    out
}

pub fn to_dnf<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    be: BooleanExpression<T>,
) -> BooleanExpression<T> {
    make_dnf(to_nnf(be))
}

fn make_dnf<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    be: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match be {
        BooleanExpression::Disjunction(v) => flatten(BooleanExpression::Disjunction(
            v.into_iter().map(make_dnf).collect(),
        )),
        BooleanExpression::Conjunction(v) => {
            let e = v
                .into_iter()
                .map(make_dnf)
                .collect::<Vec<BooleanExpression<T>>>();
            flatten(BooleanExpression::Disjunction(
                distribute_disjunctions::<T>(&e),
            ))
        }
        _ => be.clone(),
    }
}

fn distribute_disjunctions<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    v: &Vec<BooleanExpression<T>>,
) -> Vec<BooleanExpression<T>> {
    fn go<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
        out: &mut Vec<BooleanExpression<T>>,
        with: &mut Vec<BooleanExpression<T>>,
        rest: &[BooleanExpression<T>],
    ) {
        match rest {
            [head, tail @ ..] => match head {
                BooleanExpression::Disjunction(disj) => {
                    for part in disj {
                        with.push(part.clone());
                        go(out, with, tail);
                        with.pop();
                    }
                }
                _ => {
                    with.push(head.clone());
                    go(out, with, tail);
                    with.pop();
                }
            },
            _ => {
                // Turn accumulated parts into a new conjunction.
                out.push(BooleanExpression::Conjunction(with.clone()));
            }
        }
    }

    let mut out = Vec::new(); // contains only `all()`
    let mut with = Vec::new();

    go(&mut out, &mut with, v);

    out
}

pub fn flatten<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    expr: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match expr {
        BooleanExpression::Conjunction(inner) => BooleanExpression::Conjunction(
            inner
                .into_iter()
                .map(|e| flatten(e))
                .flat_map(|e| match e {
                    BooleanExpression::Conjunction(inner) => inner,
                    _ => vec![e],
                })
                .collect(),
        ),
        BooleanExpression::Disjunction(inner) => BooleanExpression::Disjunction(
            inner
                .into_iter()
                .map(|e| flatten(e))
                .flat_map(|e| match e {
                    BooleanExpression::Disjunction(inner) => inner,
                    _ => vec![e],
                })
                .collect(),
        ),
        _ => expr,
    }
}

pub fn sort<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    expr: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match expr {
        BooleanExpression::Conjunction(mut inner) => {
            inner = inner.into_iter().map(sort).collect();
            inner.sort();
            BooleanExpression::Conjunction(inner)
        }
        BooleanExpression::Disjunction(mut inner) => {
            inner = inner.into_iter().map(sort).collect();
            inner.sort();
            BooleanExpression::Disjunction(inner)
        }
        _ => expr,
    }
}

pub fn simplify<T: Clone + Debug + PartialEq + PartialOrd + Eq + Ord + Hash>(
    be: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match be {
        BooleanExpression::Conjunction(mut inner) => {
            inner = inner.into_iter().map(simplify).collect();

            let negative_contains: Vec<BooleanExpression<T>> = inner
                .iter()
                .filter_map(|x| match x {
                    BooleanExpression::Negation(box BooleanExpression::Contain(t)) => {
                        Some(BooleanExpression::Contain(t.clone()))
                    }
                    _ => None,
                })
                .collect();

            let removable_contains: Vec<BooleanExpression<T>> = inner
                .iter()
                .filter(|&x| negative_contains.contains(x))
                .flat_map(|x| vec![x.clone(), BooleanExpression::Negation(Box::new(x.clone()))])
                .collect();

            let inner: Vec<BooleanExpression<T>> = inner
                .into_iter()
                .map(|x| {
                    if removable_contains.contains(&x) {
                        BooleanExpression::False
                    } else {
                        x
                    }
                })
                .filter(|x| x != &BooleanExpression::True)
                .collect::<HashSet<_>>()
                .into_iter()
                .collect();

            if let Some(_) = inner.iter().find(|&x| x == &BooleanExpression::False) {
                BooleanExpression::False
            } else if inner.len() == 1 {
                inner[0].clone()
            } else {
                BooleanExpression::Conjunction(inner)
            }
        }
        BooleanExpression::Disjunction(mut inner) => {
            inner = inner.into_iter().map(simplify).collect();

            let negative_contains: Vec<BooleanExpression<T>> = inner
                .iter()
                .filter_map(|x| match x {
                    BooleanExpression::Negation(box BooleanExpression::Contain(t)) => {
                        Some(BooleanExpression::Contain(t.clone()))
                    }
                    _ => None,
                })
                .collect();

            let removable_contains: Vec<BooleanExpression<T>> = inner
                .iter()
                .filter(|&x| negative_contains.contains(x))
                .flat_map(|x| vec![x.clone(), BooleanExpression::Negation(Box::new(x.clone()))])
                .collect();

            let inner: Vec<BooleanExpression<T>> = inner
                .into_iter()
                .map(|x| {
                    if removable_contains.contains(&x) {
                        BooleanExpression::True
                    } else {
                        x
                    }
                })
                .filter(|x| x != &BooleanExpression::False)
                .collect::<HashSet<_>>()
                .into_iter()
                .collect();

            if inner.len() == 0 {
                BooleanExpression::True
            } else if let Some(_) = inner.iter().find(|&x| x == &BooleanExpression::True) {
                BooleanExpression::True
            } else if inner.len() == 1 {
                inner[0].clone()
            } else {
                BooleanExpression::Disjunction(inner)
            }
        }
        BooleanExpression::Negation(box BooleanExpression::True) => BooleanExpression::False,
        BooleanExpression::Negation(box BooleanExpression::False) => BooleanExpression::True,
        _ => be,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simplify() {
        let a = BooleanExpression::Contain(vec!["A"]);
        let b = BooleanExpression::Contain(vec!["B"]);
        assert_eq!(simplify(a.clone() & BooleanExpression::True), a.clone());
        assert_eq!(
            simplify(a.clone() & BooleanExpression::False),
            BooleanExpression::False
        );

        assert_eq!(simplify(a.clone() | !a.clone()), BooleanExpression::True);
        assert_eq!(simplify(a.clone() & !a.clone()), BooleanExpression::False);
        assert_eq!(
            sort(simplify(a.clone() | !b.clone())),
            a.clone() | !b.clone()
        );
        assert_eq!(
            simplify(a.clone() | BooleanExpression::True),
            BooleanExpression::True
        );
        assert_eq!(simplify(a.clone() | BooleanExpression::False), a.clone());

        assert_eq!(
            simplify(!BooleanExpression::True::<String>),
            BooleanExpression::False
        );
        assert_eq!(
            simplify(!BooleanExpression::False::<String>),
            BooleanExpression::True
        );
    }

    #[test]
    fn test_to_nnf() {
        let a = BooleanExpression::Contain(vec!["A"]);
        let b = BooleanExpression::Contain(vec!["B"]);
        let c = BooleanExpression::Contain(vec!["C"]);
        let d = BooleanExpression::Contain(vec!["D"]);
        assert_eq!(to_nnf(!(a.clone() & b.clone()),), !a.clone() | !b.clone());
        // https://www.wolframalpha.com/input?i=not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29+or+%28A+or+B%29+and+%28C+and+not+D+or+not+C+and+D%29&lang=ja
        assert_eq!(
            to_nnf(
                (!a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone()))
                    | ((a.clone() | b.clone())
                        & ((c.clone() & !d.clone()) | (!c.clone() & d.clone()))),
            ),
            ((!a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone()))
                | ((a.clone() | b.clone())
                    & ((c.clone() & !d.clone()) | (!c.clone() & d.clone()))))
        )
    }

    #[test]
    fn test_distribute_conjunctions() {
        let a = BooleanExpression::Contain(vec!["A"]);
        let b = BooleanExpression::Contain(vec!["B"]);
        let c = BooleanExpression::Contain(vec!["C"]);
        let d = BooleanExpression::Contain(vec!["D"]);
        assert_eq!(
            distribute_conjunctions(&vec![(c.clone() & !d.clone()), (!c.clone() & d.clone())]),
            vec![
                c.clone() | !c.clone(),
                c.clone() | d.clone(),
                !d.clone() | !c.clone(),
                !d.clone() | d.clone(),
            ]
        );
        assert_eq!(
            distribute_conjunctions(&vec![a.clone() & b.clone(), c.clone()]),
            vec![a.clone() | c.clone(), b.clone() | c.clone()],
        );
        assert_eq!(
            distribute_conjunctions(&vec![a.clone() & b.clone(), c.clone() & d.clone(),]),
            vec![
                a.clone() | c.clone(),
                a.clone() | d.clone(),
                b.clone() | c.clone(),
                b.clone() | d.clone(),
            ]
        );
    }

    #[test]
    fn test_cnf() {
        let a = BooleanExpression::Contain(vec!["A"]);
        let b = BooleanExpression::Contain(vec!["B"]);
        let c = BooleanExpression::Contain(vec!["C"]);
        let d = BooleanExpression::Contain(vec!["D"]);

        // https://www.wolframalpha.com/input?i=not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29+&lang=ja
        assert_eq!(
            sort(simplify(to_cnf(
                !a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone())
            ))),
            sort(simplify(flatten(
                !a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone())
            )))
        );

        assert_eq!(
            sort(simplify(to_cnf(
                (c.clone() & !d.clone()) | (!c.clone() & d.clone())
            ))),
            sort(simplify(flatten(
                (c.clone() | d.clone()) & (!c.clone() | !d.clone())
            )))
        );

        assert_eq!(
            sort(simplify(to_cnf(
                (a.clone() | b.clone()) & ((c.clone() & !d.clone()) | (!c.clone() & d.clone()))
            ))),
            sort(simplify(flatten(
                (a.clone() | b.clone()) & (c.clone() | d.clone()) & (!c.clone() | !d.clone())
            )))
        );

        // https://www.wolframalpha.com/input?i=%28not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29%29+or+%28%28A+or+B%29+and+%28C+or+D%29+and+%28not+C+or+not+D%29%29&lang=ja
        assert_eq!(
            sort(simplify(to_cnf(
                (!a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone()))
                    | ((a.clone() | b.clone())
                        & (c.clone() | d.clone())
                        & (!c.clone() | !d.clone())),
            ))),
            sort(simplify(flatten(
                (!a.clone() | !c.clone() | !d.clone())
                    & (!a.clone() | c.clone() | d.clone())
                    & (a.clone() | b.clone() | !c.clone() | d.clone())
                    & (a.clone() | b.clone() | c.clone() | !d.clone())
                    & (!b.clone() | !c.clone() | !d.clone())
                    & (!b.clone() | c.clone() | d.clone())
            )))
        );

        // https://www.wolframalpha.com/input?i=not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29+or+%28A+or+B%29+and+%28C+and+not+D+or+not+C+and+D%29&lang=ja
        assert_eq!(
            sort(simplify(to_cnf(
                (!a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone()))
                    | ((a.clone() | b.clone())
                        & ((c.clone() & !d.clone()) | (!c.clone() & d.clone()))),
            ))),
            sort(simplify(flatten(
                (!a.clone() | !c.clone() | !d.clone())
                    & (!a.clone() | c.clone() | d.clone())
                    & (a.clone() | b.clone() | !c.clone() | d.clone())
                    & (a.clone() | b.clone() | c.clone() | !d.clone())
                    & (!b.clone() | !c.clone() | !d.clone())
                    & (!b.clone() | c.clone() | d.clone())
            )))
        )
    }

    #[test]
    fn test_distribute_disjunctions() {
        let a = BooleanExpression::Contain(vec!["A"]);
        let b = BooleanExpression::Contain(vec!["B"]);
        let c = BooleanExpression::Contain(vec!["C"]);
        let d = BooleanExpression::Contain(vec!["D"]);
        assert_eq!(
            distribute_disjunctions(&vec![(c.clone() | !d.clone()), (!c.clone() | d.clone())]),
            vec![
                c.clone() & !c.clone(),
                c.clone() & d.clone(),
                !d.clone() & !c.clone(),
                !d.clone() & d.clone(),
            ]
        );
        assert_eq!(
            distribute_disjunctions(&vec![a.clone() | b.clone(), c.clone()]),
            vec![a.clone() & c.clone(), b.clone() & c.clone()],
        );
        assert_eq!(
            distribute_disjunctions(&vec![a.clone() | b.clone(), c.clone() | d.clone(),]),
            vec![
                a.clone() & c.clone(),
                a.clone() & d.clone(),
                b.clone() & c.clone(),
                b.clone() & d.clone(),
            ]
        );
    }

    #[test]
    fn test_dnf() {
        let a = BooleanExpression::Contain(vec!["A"]);
        let b = BooleanExpression::Contain(vec!["B"]);
        let c = BooleanExpression::Contain(vec!["C"]);
        let d = BooleanExpression::Contain(vec!["D"]);

        // https://www.wolframalpha.com/input?i=not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29+&lang=ja
        assert_eq!(
            sort(simplify(to_dnf(
                !a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone())
            ))),
            sort(simplify(flatten(
                (!a.clone() & !b.clone() & c.clone() & d.clone())
                    | (!a.clone() & !b.clone() & !c.clone() & !d.clone())
            )))
        );

        // https://www.wolframalpha.com/input?i=%28C+and+not+D%29+or+%28not+C+and+D%29&lang=ja
        assert_eq!(
            sort(simplify(to_dnf(
                (c.clone() & !d.clone()) | (!c.clone() & d.clone())
            ))),
            sort(simplify(flatten(
                (c.clone() & !d.clone()) | (!c.clone() & d.clone())
            )))
        );

        assert_eq!(
            sort(simplify(to_dnf(
                (a.clone() | b.clone()) & ((c.clone() & !d.clone()) | (!c.clone() & d.clone()))
            ))),
            sort(simplify(flatten(
                (a.clone() & c.clone() & !d.clone())
                    | (a.clone() & !c.clone() & d.clone())
                    | (b.clone() & c.clone() & !d.clone())
                    | (b.clone() & !c.clone() & d.clone())
            )))
        );

        // https://www.wolframalpha.com/input?i=%28not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29%29+or+%28%28A+or+B%29+and+%28C+or+D%29+and+%28not+C+or+not+D%29%29&lang=ja
        assert_eq!(
            sort(simplify(to_dnf(
                (!a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone()))
                    | ((a.clone() | b.clone())
                        & (c.clone() | d.clone())
                        & (!c.clone() | !d.clone())),
            ))),
            sort(simplify(flatten(
                (a.clone() & c.clone() & !d.clone())
                    | (a.clone() & !c.clone() & d.clone())
                    | (!a.clone() & !b.clone() & c.clone() & d.clone())
                    | (!a.clone() & !b.clone() & !c.clone() & !d.clone())
                    | (b.clone() & c.clone() & !d.clone())
                    | (b.clone() & !c.clone() & d.clone())
            )))
        );

        // https://www.wolframalpha.com/input?i=not+A+and+not+B+and+%28not+C+or+D%29+and%28C+or+not+D%29+or+%28A+or+B%29+and+%28C+and+not+D+or+not+C+and+D%29&lang=ja
        assert_eq!(
            sort(simplify(to_dnf(
                (!a.clone() & !b.clone() & (!c.clone() | d.clone()) & (c.clone() | !d.clone()))
                    | ((a.clone() | b.clone())
                        & ((c.clone() & !d.clone()) | (!c.clone() & d.clone()))),
            ))),
            sort(simplify(flatten(
                (a.clone() & c.clone() & !d.clone())
                    | (a.clone() & !c.clone() & d.clone())
                    | (!a.clone() & !b.clone() & c.clone() & d.clone())
                    | (!a.clone() & !b.clone() & !c.clone() & !d.clone())
                    | (b.clone() & c.clone() & !d.clone())
                    | (b.clone() & !c.clone() & d.clone())
            )))
        )
    }
}
