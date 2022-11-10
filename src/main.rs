use std::env;
use std::fs::File;
use std::io::BufReader;
use smt2parser::{CommandStream, concrete};

fn main() {
    let args: Vec<String> = env::args().collect();
    let file_path = &args[1];

    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);

    let stream = CommandStream::new(
        reader,
        concrete::SyntaxBuilder,
        Some("optional/path/to/file".to_string()),
    );
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    // assert!(matches!(commands[..], [
    //     concrete::Command::Echo {..},
    //     concrete::Command::Exit,
    // ]));
    assert_eq!(commands[0].to_string(), "(echo \"Hello world!\")");
}
