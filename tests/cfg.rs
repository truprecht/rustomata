extern crate log_domain;
extern crate rustomata;
extern crate rustomata_grammar;
extern crate rustomata_automaton;
#[macro_use]
extern crate rustomata_ctf;

use log_domain::LogDomain;
// TODO: Uncomment once PushDownAutomaton::FromStr has been implemented
// use std::collections::HashSet;
use std::fs::File;
use std::io::Read;

use rustomata_ctf::equivalence_classes::EquivalenceRelation;
use rustomata_ctf::relabel::RlbElement;
use rustomata_ctf::ApproximationStrategy;
use rustomata_automaton::push_down_automaton::{*, from_cfg::PushState};
use rustomata_grammar::cfg::*;
use rustomata_automaton::recognisable::*;
// TODO: Uncomment once PushDownAutomaton::FromStr has been implemented
// use rustomata_automaton::recognisable::automaton::Automaton;

fn cfg_from_file(grammar_file_path: &str) -> CFG<String, String, LogDomain<f64>> {
    let mut grammar_file = File::open(grammar_file_path).unwrap();
    let mut grammar_string = String::new();
    let _ = grammar_file.read_to_string(&mut grammar_string);
    grammar_string.parse().unwrap()
}

fn example_equivalence_relation() -> EquivalenceRelation<String, String> {
    let mut relation_file = File::open("examples/example.classes").unwrap();
    let mut relation_string = String::new();
    let _ = relation_file.read_to_string(&mut relation_string);

    relation_string.parse().unwrap()
}

#[test]
fn test_relabel_pushdown_correctness() {
    let automaton = PushDownAutomaton::from(cfg_from_file("examples/example2.cfg"));
    let rel = example_equivalence_relation();
    let mapping = |ps: &PushState<_, _>| ps.map(|nt| rel.project(nt));
    let rlb = RlbElement::new(&mapping);
    let (relabelled_automaton, _) = rlb.approximate_automaton(&automaton);

    let true_positives_and_true_negatives =
        vec!["aab", "bba", "aaabb", "aabba", "", "aa", "aaab", "bbbbbb"];

    for input in true_positives_and_true_negatives {
        let word: Vec<_> = String::from(input).chars().map(|x| x.to_string()).collect();
        assert_eq!(
            automaton.recognise(word.clone()).next().is_some(),
            relabelled_automaton.recognise(word).next().is_some()
        );
    }

    let false_positives = vec!["aaa", "bbb", "aabaa", "abaaa"];

    for word in false_positives {
        let input: Vec<_> = String::from(word).chars().map(|x| x.to_string()).collect();
        assert_eq!(false, automaton.recognise(input.clone()).next().is_some());
        assert_eq!(true, relabelled_automaton.recognise(input).next().is_some());
    }
}

#[test]
fn test_cfg_from_str_correctness() {
    let rule_s0 = CFGRule {
        head: String::from("S"),
        composition: CFGComposition {
            composition: vec![
                LetterT::Value(String::from("a")),
                LetterT::Label(String::from("S")),
                LetterT::Value(String::from("b")),
            ],
        },
        weight: LogDomain::new(0.4).unwrap(),
    };
    let rule_s1 = CFGRule {
        head: String::from("S"),
        composition: CFGComposition {
            composition: vec![],
        },
        weight: LogDomain::new(0.6).unwrap(),
    };
    let control_grammar = CFG {
        initial: vec![String::from("S")],
        rules: vec![rule_s0, rule_s1],
    };

    let grammar = cfg_from_file("examples/example.cfg");
    assert_eq!(control_grammar.clone(), grammar.clone());

    let control_automaton = PushDownAutomaton::from(control_grammar);
    let automaton = PushDownAutomaton::from(grammar);
    let inputs = vec!["", "aabb", "abb", "aab"];

    for input in inputs {
        let word: Vec<_> = String::from(input).chars().map(|x| x.to_string()).collect();
        assert_eq!(
            control_automaton.recognise(word.clone()).next().is_some(),
            automaton.recognise(word).next().is_some()
        );
    }
}

// TODO: Uncomment once PushDownAutomaton::FromStr has been implemented
/*
#[test]
fn test_pushdown_automaton_from_str() {
    use PushDownInstruction::Replace;

    let unprocessed_transitions = vec![
        ("a", Replace { current_val: vec!["(a)".to_string()], new_val: vec![] }, 1.0),
        ("b", Replace { current_val: vec!["(b)".to_string()], new_val: vec![] }, 1.0),
        ("",  Replace { current_val: vec!["(S)".to_string()], new_val: vec![] }, 0.6),
        ("",  Replace { current_val: vec!["(S)".to_string()], new_val: vec![
            "(b)".to_string(), "(S)".to_string(), "(a)".to_string(),
        ] }, 0.4),
        ("",  Replace { current_val: vec!["I".to_string()], new_val: vec!["(S)".to_string()] }, 1.0),
    ];

    let mut transitions = Vec::new();
    for (terminal, instruction, weight) in unprocessed_transitions {
        transitions.push(Transition {
            word: terminal.chars().map(|x| x.to_string()).collect(),
            instruction,
            weight: LogDomain::new(weight).unwrap()
        });
    }
    let control_automaton = PushDownAutomaton::new(transitions, PushDown::new("I".to_string(), "@".to_string()));

    let mut automaton_file = File::open("examples/example.pda").unwrap();
    let mut automaton_string = String::new();
    let _ = automaton_file.read_to_string(&mut automaton_string);
    let automaton: PushDownAutomaton<String, String, LogDomain<f64>> = automaton_string.parse().unwrap();

    assert_eq!(
        control_automaton.initial(),
        automaton.initial()
    );
    assert_eq!(
        control_automaton.list_transitions().collect::<HashSet<_>>(),
        automaton.list_transitions().collect::<HashSet<_>>()
    );
}
*/

#[test]
fn test_cfg_recognise_legal_terminal_symbols() {
    let automaton = PushDownAutomaton::from(cfg_from_file("examples/example.cfg"));
    let legal_inputs = vec![("", true), ("aabb", true), ("aab", false), ("a", false)];

    for (legal_input, control_acceptance) in legal_inputs {
        let legal_word: Vec<_> = String::from(legal_input)
            .chars()
            .map(|x| x.to_string())
            .collect();
        assert_eq!(
            control_acceptance,
            automaton.recognise(legal_word).next().is_some()
        );
    }
}

#[test]
fn test_cfg_recognise_illegal_terminal_symbols() {
    let automaton = PushDownAutomaton::from(cfg_from_file("examples/example.cfg"));
    let illegal_inputs = vec!["aacc"];

    for illegal_input in illegal_inputs {
        let illegal_word: Vec<_> = String::from(illegal_input)
            .chars()
            .map(|x| x.to_string())
            .collect();
        assert!(automaton.recognise(illegal_word).next().is_none());
    }
}
