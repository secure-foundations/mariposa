use smt2parser::concrete;
use smt2parser::concrete::{QualIdentifier, Term};

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
            if let QualIdentifier::Simple { identifier } = qual_identifier {
                if let concrete::Identifier::Simple { symbol } = identifier {
                    if symbol.0 == "=>" || symbol.0 == "implies" || symbol.0 == "and" || symbol.0 == "or" || symbol.0 == "=" {
                        assert!(arguments.len() == 2);
                        print!("{}(=>\n", " ".repeat(indent));
                        print_prop_skeleton(&arguments[0], indent + 1);
                        print_prop_skeleton(&arguments[1], indent + 1);
                        print!("{})\n", " ".repeat(indent));
                        return;
                    }
                    if symbol.0 == "not" {
                        assert!(arguments.len() == 1);
                        print!("{}(not\n", " ".repeat(indent));
                        print_prop_skeleton(&arguments[0], indent + 1);
                        print!("{})\n", " ".repeat(indent));
                        return;
                    }
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
