use grammars::pmcfg::{PMCFGRule, VarT};

use std::{ hash::Hash, collections::HashSet };
use integeriser::{HashIntegeriser, Integeriser};
use util::{IntMap, IntSet};
use fnv::{FnvHashMap, FnvHashSet};

type RuleId = usize;
type CachedNt = usize;

/// Serializable filter for grammar rules.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedFilterPersistentStorage<T>
where
    T: Eq + Hash
{
    free_rules: IntSet, // rules without rhs nts and terminals
    free_nts: IntSet, // lhs nonterminals of those rules
    
    // rules with nts on rhs, no terminals
    only_nt: IntMap<Vec<(Vec<CachedNt>, RuleId, CachedNt)>>,
    // rules with no nts on rhs, but terminals
    only_t: FnvHashMap<T, Vec<(Vec<T>, RuleId, CachedNt)>>,
    // rules with nts and terminals
    nt_and_t: FnvHashMap<T, Vec<(Vec<T>, Vec<CachedNt>, RuleId, CachedNt)>>
}

impl<T> CachedFilterPersistentStorage<T>
where
    T: Clone + Eq + Hash
{
    pub fn new<'a, N, W>(rules: impl Iterator<Item=(usize, &'a PMCFGRule<N, T, W>)> + 'a) -> Self 
    where
        N: Hash + Eq + 'a,
        T: 'a,
        W: 'a
    {
        let mut integeriser: HashIntegeriser<&N> = HashIntegeriser::new();
        let mut free_rules: IntSet = IntSet::default();
        let mut free_nts: IntSet = IntSet::default();

        let mut only_nt = IntMap::default();
        let mut only_t = FnvHashMap::default();
        let mut nt_and_t = FnvHashMap::default();

        for (rid, rule) in rules {
            let nid = integeriser.integerise(&rule.head);
            let mut ts = (&rule.composition).into_iter()
                               .flat_map(|v| v)
                               .filter_map(|vart| if let &VarT::T(ref t) = vart { Some(t.clone()) } else { None })
                               .collect::<HashSet<_>>()
                               .into_iter()
                               .collect::<Vec<_>>();
            if rule.tail.is_empty() {
                if ts.is_empty()  {
                    free_rules.insert(rid);
                    free_nts.insert(nid);
                } else {
                    only_t.entry(ts.remove(0))
                          .or_insert_with(Vec::new)
                          .push((ts, rid, nid));
                }
            } else {
                let i_rhs: Vec<usize> = rule.tail.iter().map(|i| integeriser.integerise(i))
                                            .collect::<HashSet<usize>>().into_iter().collect();
                if ts.is_empty()  {
                    for rhs_index in 0..(i_rhs.len()) {
                        let mut rhs_remainder = i_rhs.clone();
                        only_nt.entry(rhs_remainder.remove(rhs_index))
                               .or_insert_with(Vec::new)
                               .push((rhs_remainder, rid, nid));
                    }
                } else {
                    nt_and_t.entry(ts.remove(0))
                            .or_insert_with(Vec::new)
                            .push((ts, i_rhs, rid, nid));
                }
            }
        }

        CachedFilterPersistentStorage{
            free_rules,
            free_nts,
            only_nt,
            only_t,
            nt_and_t
        }
    }

    pub fn instantiate(&self, word: &[T]) -> IntSet {
        let ts: FnvHashSet<&T> = word.iter().collect::<FnvHashSet<_>>();

        let mut free_nts = self.free_nts.clone();
        let mut free_rules = self.free_rules.clone();
        let mut only_nt = self.only_nt.clone();

        for t in &ts {
            for &(ref ts_to_check, rid, nid) in self.only_t.get(*t).into_iter().flat_map(|v| v) {
                if ts_to_check.iter().all(|symbol| ts.contains(&symbol)) {
                    free_nts.insert(nid);
                    free_rules.insert(rid);
                }
            }
            for &(ref ts_to_check, ref nts, rid, nid) in self.nt_and_t.get(*t).into_iter().flat_map(|v| v) {
                if ts_to_check.iter().all(|symbol| ts.contains(&symbol)) {
                    for nts_index in 0..(nts.len()) {
                        let mut nts_without_index = nts.clone();
                        let nts_at_index = nts_without_index.remove(nts_index);
                        only_nt.entry(nts_at_index)
                               .or_insert_with(Vec::new)
                               .push((nts_without_index, rid, nid));
                    }
                }
            }
        }

        let mut runtime_stack = free_nts.iter().cloned().collect::<Vec<_>>();

        while let Some(nt) = runtime_stack.pop() {
            for &(ref rhs, rule, lhs) in only_nt.get(&nt).into_iter().flat_map(|v| v) {
                if !free_rules.contains(&rule) && rhs.iter().all(|a| free_nts.contains(a)) {
                    free_rules.insert(rule);
                    if free_nts.insert(lhs) { runtime_stack.push(lhs); }
                }
            }
        }

        free_rules
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use grammars::pmcfg::Composition;
    use integeriser::{HashIntegeriser, Integeriser};

    #[test]
    fn filter() {
        let rules = vec![
            PMCFGRule{ head: "A", tail: vec!["A"], weight: 1f64, composition: Composition::from(vec![vec![VarT::T(1), VarT::Var(0,0)], vec![VarT::Var(0, 1), VarT::T(2)]])},
            PMCFGRule{ head: "A", tail: vec!["B"], weight: 1f64, composition: Composition::from(vec![vec![VarT::T(1), VarT::Var(0,0)], vec![VarT::Var(0, 1), VarT::T(2)]])},
            PMCFGRule{ head: "A", tail: vec![], weight: 1f64, composition: Composition::from(vec![vec![VarT::T(0)], vec![VarT::T(0)]])},
            PMCFGRule{ head: "B", tail: vec![], weight: 1f64, composition: Composition::from(vec![vec![VarT::T(3)], vec![VarT::T(3)]])}
        ];
        
        let mut integeriser = HashIntegeriser::new();
        
        for rule in rules {
            integeriser.integerise(rule);
        }

        let filter = CachedFilterPersistentStorage::new(integeriser.values().iter().enumerate());

        assert_eq!(filter.clone().instantiate(&[]), vec![].into_iter().collect::<IntSet>());
        assert_eq!(filter.clone().instantiate(&[1]), vec![].into_iter().collect::<>());
        assert_eq!(filter.clone().instantiate(&[2]), vec![].into_iter().collect::<>());
        assert_eq!(filter.clone().instantiate(&[1, 2]), vec![].into_iter().collect::<>());
        assert_eq!(filter.clone().instantiate(&[0, 1]), vec![2].into_iter().collect::<>());
        assert_eq!(filter.clone().instantiate(&[0, 1, 2]), vec![0, 2].into_iter().collect::<>());
        assert_eq!(filter.clone().instantiate(&[1, 2, 3]), vec![0, 1, 3].into_iter().collect::<>());
        assert_eq!(filter.clone().instantiate(&[0, 1, 2, 3]), vec![0, 1, 2, 3].into_iter().collect::<>());
    }
}