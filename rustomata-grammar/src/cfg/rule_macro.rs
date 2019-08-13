#[macro_export]
macro_rules! cfg_rule {
    (
        $lhs:expr => [ $( $vart:expr ),* ] # $w:expr
    ) => {{
        use $crate::cfg::{CFGComposition, CFGRule};
        let head = $lhs;
        let composition = CFGComposition{ composition: vec![ $( $vart ),* ] };
        let weight = $w;

        CFGRule {
            head,
            composition,
            weight
        }
    }}
}

#[cfg(test)]
mod test {
    use crate::cfg::{CFGRule, LetterT, CFGComposition};
    use self::LetterT::*;
    
    #[test]
    fn rule_macro () {
        let r = cfg_rule!("A" => [Label("A"), Value("a"), Value("b"), Label("B")] # 1usize );
        assert_eq!(
            r,
            CFGRule {
                head: "A",
                composition: CFGComposition{ composition: vec![Label("A"), Value("a"), Value("b"), Label("B")] },
                weight: 1usize
            }
        );
        let r: CFGRule<&str, &str, usize> = cfg_rule!("A" => [] # 1usize);
        assert_eq!(
            r,
            CFGRule {
                head: "A",
                composition: CFGComposition{ composition: vec![] },
                weight: 1usize
            }
        )
    }
}