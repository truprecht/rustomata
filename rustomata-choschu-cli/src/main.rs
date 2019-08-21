use clap::clap_app;
use log_domain::LogDomain;
use num_traits::{One, Zero};
use rustomata_grammar::{lcfrs::Lcfrs,
                          pmcfg::negra::{to_negra, DumpMode, noparse}};
use rustomata_grammar::lcfrs::from_discodop::DiscoDopGrammar;
use rustomata_choschu::{CSRepresentation, result::ParseResult};
use std::io::{Read, stdin, BufRead};
use std::fs::File;
use std::str::FromStr;

#[cfg(feature="serialization")]
use ::{
    flate2::{read, write, Compression},
    bincode::{deserialize_from, serialize_into, Infinite},
    std::io::stdout,
};

pub enum GrammarType { Disco, Plain, CsRep }

impl FromStr for GrammarType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "disco" => Ok(GrammarType::Disco),
            "plain" => Ok(GrammarType::Plain),
            "cs"    => Ok(GrammarType::CsRep),
            _       => Err(()),
        }
    }
}

fn split_line<'a>(
    line: &'a str,
    with_line_number: bool,
    default_line_number: usize,
) -> (usize, impl Iterator<Item = &'a str> + 'a) {
    let mut word_iterator = line.split_whitespace();

    let line_number = if with_line_number {
        word_iterator
            .next()
            .expect("missing line number")
            .parse()
            .expect("invalid line numer")
    } else {
        default_line_number
    };

    (line_number, word_iterator)
}

fn split_pos<'a>(
    words: impl Iterator<Item = &'a str> + 'a,
    with_pos: bool,
) -> (Vec<String>, DumpMode<String>) {
    if with_pos {
        let (pos, ws) = words
            .map(|wp| {
                let mut it = wp.rsplitn(2, '/');
                (
                    it.next().unwrap().to_string(),
                    it.next().expect("missing pos annotation").to_string(),
                )
            })
            .unzip();
        (pos, DumpMode::FromPos(ws))
    } else {
        (words.map(|s| s.to_string()).collect(), DumpMode::Default)
    }
}

#[cfg(feature="serialization")]
fn read_cs_file(grfile: File) -> CSRepresentation<String, String, LogDomain<f64>> {
    deserialize_from(&mut read::GzDecoder::new(grfile), Infinite).unwrap()
}

#[cfg(not(feature="serialization"))]
fn read_cs_file(_: File) -> CSRepresentation<String, String, LogDomain<f64>> {
    panic!("serialization feature was not activated during compilation")
}

fn read_grammar_obj(mut grfile: File, gt: GrammarType, sxlen: usize, o_lexer_file: Option<File>) -> CSRepresentation<String, String, LogDomain<f64>> {
    match gt {
        GrammarType::CsRep => {
            read_cs_file(grfile)
        },
        GrammarType::Disco 
        | GrammarType::Plain => {
            // read grammar from file
            let grammar_string = {
                let mut grstr = String::new();
                grfile.read_to_string(&mut grstr).unwrap();
                grstr
            };

            let grobj = if let GrammarType::Disco = gt {
                let dgmr: DiscoDopGrammar<_, _, _> = grammar_string.parse().unwrap();
                if let Some(mut lexer_file) = o_lexer_file {
                    let mut lexer_string = String::new();
                    lexer_file.read_to_string(&mut lexer_string).unwrap();
                    dgmr.with_lexer(lexer_string.parse().unwrap()).into()
                } else {
                    dgmr.with_default_lexer().into()
                }
            } else {
                grammar_string.parse::<Lcfrs<String, String, LogDomain<f64>>>().unwrap()
            };

            CSRepresentation::new(grobj, sxlen)
        },
    }
}

fn main() -> Result<(), ::std::io::Error> {
    let matches = clap_app!(choschu =>
        (version: "0.1")
        (author: "Thomas Ruprech <thomas.ruprecht@tu-dresden.de>")
        (about: "Reference implementation of a Chomsky-Schützenberger parser for weighted multiple context-free grammars")
        (@subcommand extract =>
            (about: "Extract an intermediate processed Chomsky-Schützenberger representation from a grammar via stdin")
            (@arg type: -t --type +takes_value "the type of the given grammar (disco|plain)")
            (@arg sxlen: -s --sxlen +takes_value "compute sx estimate for specified length")
            (@arg lexer: -l --lexer +takes_value "gives the lexer for the disco-dop grammar")
        )
        (@subcommand parse =>
            (about: "Parse sentences given via stdin using a given grammar")
            (@arg GRAMMAR: +required "Either an extracted representation or a grammar")
            (@arg type: -t --type +takes_value "the type of the given grammar (disco|plain|cs)")
            (@arg lexer: -l --lexer +takes_value "gives the lexer for the disco-dop grammar")
            (@arg k: -k --kbest +takes_value "puts the 'k' into k-best parsing")
            (@arg beam: --beamwidth +takes_value "use beam search with specified beam width")
            (@arg threshold: --beamthresh +takes_value "use beam search with limited weight range")
            (@arg sxlen: -s --sxlen +takes_value "compute sx estimate for specified length")
            (@arg fallback: -f --fallback +takes_value "use a fallback result if no parse is found")
            (@arg candidates: -c --candidates +takes_value "limit the number of enumerated Dyck words")
            (@arg debug: -d --debug "print debug messages to stderr")
            (@arg lines: --withlines "give sentence numers")
            (@arg pos: --withpos "parse pos anotations instead of words")
        )
    ).get_matches();

    match matches.subcommand() {
        ("extract", Some(_options)) => {
            #[cfg(feature="serialization")]
            {
                // get options
                let sxlen: usize
                    = _options.value_of("sxlen").and_then(|ustr| ustr.parse().ok()).unwrap_or(0);
                let grammar_type: GrammarType
                    = _options.value_of("type").and_then(|tstr| tstr.parse().ok()).unwrap();
                let lexer_file: Option<File>
                    = _options.value_of("lexer").map(|lfl| File::open(lfl).unwrap());

                // get grammar object
                let grfile = File::open(_options.value_of("GRAMMAR").unwrap())?;
                let csobj = read_grammar_obj(grfile, grammar_type, sxlen, lexer_file);

                serialize_into(
                    &mut write::GzEncoder::new(stdout(), Compression::best()),
                    &csobj,
                    bincode::Infinite,
                ).unwrap();
            }
            
            #[cfg(not(feature="serialization"))]
            panic!("serialization feature was not activated during compilation")
        },
        ("parse", Some(options)) => {
            // get options
            let beam_width: Option<usize>
                = options.value_of("beam").map(|s| s.parse().unwrap());
            let beam_threshold: Option<LogDomain<f64>>
                = options.value_of("threshold").map(|s| s.parse().unwrap());
            let candidates: Option<usize>
                = options.value_of("candidates").map(|s| s.parse().unwrap());
            let fallback: Option<LogDomain<f64>>
                = options.value_of("fallback").map(|s| s.parse().unwrap());
            let k: usize
                = options.value_of("k").map(|s| s.parse().unwrap()).unwrap_or(1);
            let sxlen: usize
                = options.value_of("sxlen").and_then(|ustr| ustr.parse().ok()).unwrap_or(0);
            let grammar_type: GrammarType
                = options.value_of("type").and_then(|tstr| tstr.parse().ok()).unwrap();
            let lexer_file: Option<File>
                = options.value_of("lexer").map(|lfl| File::open(lfl).unwrap());

            // get grammar object
            let grfile = File::open(options.value_of("GRAMMAR").unwrap())?;
            let csobj = read_grammar_obj(grfile, grammar_type, sxlen, lexer_file);

            // configure parser
            let mut parser = csobj.build_generator();
            if let Some(beam) = beam_width { parser.set_beam(beam) };
            if let Some(delta) = beam_threshold { parser.set_delta(delta) };
            if let Some(candidates) = candidates { parser.set_candidates(candidates) };
            if let Some(fallback_penalty) = fallback {
                assert!(fallback_penalty != LogDomain::zero() && fallback_penalty != LogDomain::one());
                parser.allow_root_prediction();
                parser.set_fallback_penalty(fallback_penalty);
            }

            for (i, sentence) in stdin().lock().lines().flatten().enumerate() {
                let (i, words) = split_line(&sentence, options.is_present("lines"), i);
                let (words, negra_mode) = split_pos(words, options.is_present("pos"));

                if options.is_present("debug") {
                    let tuple = parser.debug(words.as_slice());
                    let (status, enum_trees, tree) = match tuple.3 {
                        ParseResult::Ok((t, n)) => ("parse", n, to_negra(&t, i, negra_mode)),
                        ParseResult::Fallback((t, n)) => ("fallback", n, to_negra(&t, i, negra_mode)),
                        ParseResult::None => ("noparse", 0, noparse(&words, i, negra_mode))
                    };
                    eprintln!("{} {} {:?} {} {}", tuple.0, tuple.1, tuple.2, status, enum_trees);
                    println!("{}", tree);
                } else {
                    match parser.parse(words.as_slice()) {
                        ParseResult::Ok(ds) => {
                            for d in ds.take(k) {
                                println!("{}", to_negra(&d.into_iter().map(|(k, v)| (k, v.clone())).collect(), i, negra_mode.clone()));
                            }
                        },
                        ParseResult::Fallback(d) => {
                            println!("{}", to_negra(&d, i, negra_mode));
                        },
                        ParseResult::None => {
                            println!("{}", noparse(&words, i, negra_mode));
                        }
                    }
                }
            }
        },
        _ => unimplemented!()
    }

    Ok(())
}