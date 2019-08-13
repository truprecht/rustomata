#[macro_export]
macro_rules! pmcfg_rule {
    (
        $lhs:expr => [ $( [ $( $vart:expr ),* ] ),* ] ( $( $rhs:expr ),* ) # $w:expr
    ) => {{
        use $crate::pmcfg::PMCFGRule;
        let head = $lhs;
        let composition = vec![$( vec![ $( $vart ),* ] ),* ].into();
        let tail = vec![ $( $rhs ),* ];
        let weight = $w;

        PMCFGRule {
            head,
            composition,
            tail,
            weight
        }
    }}
}

#[cfg(test)]
mod test {
    use crate::pmcfg::{PMCFGRule, VarT};
    use self::VarT::*;
    
    #[test]
    fn rule_macro () {
        let r = pmcfg_rule!("A" => [[Var(0,0), T("b")], [Var(1,0)]] ("B", "C") # 1usize );
        assert_eq!(
            r,
            PMCFGRule {
                head: "A",
                tail: vec!["B", "C"],
                composition: vec![vec![Var(0,0), T("b")], vec![Var(1,0)]].into(),
                weight: 1usize
            }
        );
        let r: PMCFGRule<&str, &str, usize> = pmcfg_rule!("A" => [] () # 1usize);
        assert_eq!(
            r,
            PMCFGRule {
                head: "A",
                tail: vec![],
                composition: vec![].into(),
                weight: 1usize
            }
        )
    }
}