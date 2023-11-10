use smt2parser::concrete;
use smt2parser::concrete::Term;

use crate::term_match::match_simple_qual_identifier;

pub fn print_prop_skeleton(term: &concrete::Term, indent: usize) {
    match term {
        Term::Constant(_) => {
            println!("{}{}", " ".repeat(indent), term);
        }
        Term::QualIdentifier(_) => {
            println!("{}{}", " ".repeat(indent), term);
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if let Some(symbol) = match_simple_qual_identifier(qual_identifier) {
                if symbol.0 == "=>"
                    || symbol.0 == "implies"
                    || symbol.0 == "and"
                    || symbol.0 == "or"
                    || symbol.0 == "="
                    || symbol.0 == "not"
                {
                    print!("{}({}\n", " ".repeat(indent), symbol.0);
                    for arg in arguments {
                        print_prop_skeleton(arg, indent + 1);
                    }
                    print!("{})\n", " ".repeat(indent));
                    return;
                }
            }
            println!("{}{}", " ".repeat(indent), term);
        }
        Term::Let { var_bindings, term } => {
            print!("{}(let (\n", " ".repeat(indent));
            for (var, binding) in var_bindings {
                print!("{}({}\n", " ".repeat(indent + 1), var);
                print_prop_skeleton(binding, indent + 2);
                print!("{})\n", " ".repeat(indent + 1));
            }
            print!("{}) in\n", " ".repeat(indent + 1));
            print_prop_skeleton(term, indent + 1);
            print!("{})\n", " ".repeat(indent));
        }
        Term::Forall { vars, term } => {
            print!("{}(forall (", " ".repeat(indent));
            vars.iter().for_each(|(var, sort)| {
                print!("({} {})", var, sort);
            });
            print!(")\n");
            print_prop_skeleton(term, indent + 1);
            print!("{})\n", " ".repeat(indent));
        }
        Term::Exists { vars, term } => {
            print!("{}(exists (", " ".repeat(indent));
            vars.iter().for_each(|(var, sort)| {
                print!("({} {})", var, sort);
            });
            print!(")\n");
            print_prop_skeleton(term, indent + 1);
            print!("{})\n", " ".repeat(indent));
        }
        Term::Match { term: _, cases: _ } => {
            panic!("TODO match cases")
        }
        Term::Attributes { term, attributes } => {
            print!("{}(!\n", " ".repeat(indent));
            print_prop_skeleton(term, indent + 1);
            attributes.iter().for_each(|(k, v)| {
                print!("{} {} {}\n", " ".repeat(indent), k, v);
            });
            print!("{})\n", " ".repeat(indent));
        }
    }
}
