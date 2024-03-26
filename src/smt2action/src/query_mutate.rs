use std::collections::BTreeMap;

use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaCha8Rng;
use smt2parser::{concrete, renaming, visitors};

// fn get_assert_intervals(commands: &Vec<concrete::Command>) -> Vec<usize> {
//     let mut indices = Vec::new();
//     for (pos, command) in commands.iter().enumerate() {
//         if let concrete::Command::Assert { .. } = command {
//             indices.push(pos);
//         }
//     }

//     let mut i = 0;
//     let mut prev = usize::MAX - 1;
//     let mut inter = false;

//     // sentinel index
//     indices.push(prev);
//     let mut intervals = Vec::new();

//     while i < indices.len() {
//         let cur = indices[i];
//         let con = prev + 1 == cur;
//         if !inter && con {
//             intervals.push(prev);
//             inter = true;
//         } else if inter && !con {
//             intervals.push(prev);
//             inter = false;
//         }
//         prev = cur;
//         i += 1;
//     }

//     intervals
// }

/// Lower the asserts to the end of the commands (before the check-sat command)
fn lower_asserts(commands: &mut Vec<concrete::Command>, rng: &mut ChaCha8Rng) {
    let check = commands.pop().unwrap();
    assert!(check == concrete::Command::CheckSat);

    let mut temp = Vec::new();
    std::mem::swap(commands, &mut temp);

    // partition the commands into asserts and non-asserts
    let (mut asserts, non_asserts): (_, Vec<_>) = temp
    .into_iter()
    .partition(|s| matches!(s, concrete::Command::Assert { .. }));
    
    // shuffle the asserts
    asserts.shuffle(rng);

    commands.extend(non_asserts);
    commands.extend(asserts);
    commands.push(check);
}

pub fn shuffle_commands(commands: &mut Vec<concrete::Command>, seed: u64, lower: bool) {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);

    if lower {
        lower_asserts(commands, &mut rng);
        return;
    }

    let mut in_assert = false;
    let mut intervals = Vec::new();
    let mut cur_start = 0;

    for (pos, command) in commands.iter().enumerate() {
        if let concrete::Command::Assert { .. } = command {
            if !in_assert {
                cur_start = pos;
            }
            in_assert = true;
        } else {
            if in_assert && cur_start != pos {
                intervals.push((cur_start, pos));
            }
            in_assert = false;
        }
    }

    intervals.into_iter().for_each(|(start, end)| {
        (&mut (*commands)[start..end]).shuffle(&mut rng);
    });}

pub fn rename_symbols(commands: &mut Vec<concrete::Command>, seed: u64) {
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
