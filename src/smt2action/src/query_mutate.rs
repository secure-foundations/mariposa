use std::collections::BTreeMap;

use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaCha8Rng;
use smt2parser::{concrete, renaming, visitors};

fn get_assert_intervals(commands: &Vec<concrete::Command>) -> Vec<usize> {
    let mut indices = Vec::new();
    for (pos, command) in commands.iter().enumerate() {
        if let concrete::Command::Assert { .. } = command {
            indices.push(pos);
        }
    }

    let mut i = 0;
    let mut prev = usize::MAX - 1;
    let mut inter = false;

    // sentinel index
    indices.push(prev);
    let mut intervals = Vec::new();

    while i < indices.len() {
        let cur = indices[i];
        let con = prev + 1 == cur;
        if !inter && con {
            intervals.push(prev);
            inter = true;
        } else if inter && !con {
            intervals.push(prev);
            inter = false;
        }
        prev = cur;
        i += 1;
    }

    intervals
}

pub fn shuffle_asserts(commands: &mut Vec<concrete::Command>, seed: u64) {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);

    let intervals = get_assert_intervals(&commands);
    let mut i = 0;
    while i < intervals.len() {
        let start = intervals[i];
        let end = intervals[i + 1] + 1;
        // sanity check the interval
        for j in start..end {
            assert!(matches!(commands[j], concrete::Command::Assert { .. }));
        }
        (&mut (*commands)[start..end]).shuffle(&mut rng);
        i += 2;
    }
}

pub fn normalize_symbols(commands: &mut Vec<concrete::Command>, seed: u64) {
    let randomization_space = BTreeMap::from([
        (visitors::SymbolKind::Variable, usize::MAX),
        (visitors::SymbolKind::Constant, usize::MAX),
        (visitors::SymbolKind::Function, usize::MAX),
        (visitors::SymbolKind::Sort, usize::MAX),
        (visitors::SymbolKind::Datatype, usize::MAX),
        (visitors::SymbolKind::TypeVar, usize::MAX),
        (visitors::SymbolKind::Constructor, usize::MAX),
        (visitors::SymbolKind::Selector, usize::MAX),
    ]);
    let config = renaming::SymbolNormalizerConfig {
        randomization_space,
        randomization_seed: seed,
    };
    let mut normalizer = renaming::SymbolNormalizer::new(concrete::SyntaxBuilder, config);
    let temp: Vec<concrete::Command> = commands
        .drain(..)
        .into_iter()
        .map(|c| c.accept(&mut normalizer).unwrap())
        .collect();
    commands.extend(temp);
}
