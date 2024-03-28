use fxhash::FxHashMap;
use typed_index_collections::TiVec;

use crate::{
    Result,
    items::{ENodeIdx, EqualityExpl, InstIdx, StackIdx, TermIdx, BlameKind}, Error
};

use super::stack::Stack;

#[derive(Debug, Default)]
pub struct EGraph {
    term_to_enode: FxHashMap<TermIdx, ENodeIdx>,
    enodes: TiVec<ENodeIdx, ENode>,
}

impl EGraph {
    pub fn new_enode(
        &mut self,
        created_by: Option<InstIdx>,
        term: TermIdx,
        z3_generation: Option<u32>,
        stack: &Stack,
    ) -> Result<ENodeIdx> {
        // TODO: why does this happen sometimes?
        // if created_by.is_none() && z3_generation.is_some() {
        //     debug_assert_eq!(
        //         z3_generation.unwrap(),
        //         0,
        //         "enode with no creator has non-zero generation"
        //     );
        // }
        self.enodes.raw.try_reserve(1)?;
        let enode = self.enodes.push_and_get_key(ENode {
            frame: stack.active_frame(),
            created_by,
            owner: term,
            z3_generation,
            equalities: Vec::new(),
        });
        self.term_to_enode.try_reserve(1)?;
        let _old = self.term_to_enode.insert(term, enode);
        // TODO: why does this happen sometimes?
        // if let Some(old) = old {
        //     assert!(self.enodes[old].frame.is_some());
        //     assert!(!stack.stack_frames[self.enodes[old].frame.unwrap()].active);
        // }
        Ok(enode)
    }

    pub fn get_enode(&self, term: TermIdx, stack: &Stack) -> Result<ENodeIdx> {
        let enode = *self.term_to_enode.get(&term).ok_or_else(|| Error::UnknownEnode(term))?;
        let frame = self.enodes[enode].frame;
        // This cannot be an enode if it points to a popped stack frame
        if frame.is_some_and(|f| !stack.stack_frames[f].active) {
            Err(Error::EnodePoppedFrame(frame.unwrap()))
        } else {
            Ok(enode)
        }
    }

    pub fn get_owner(&self, enode: ENodeIdx) -> TermIdx {
        self.enodes[enode].owner
    }

    pub fn new_equality(&mut self, from: ENodeIdx, expl: EqualityExpl, stack: &Stack) -> Result<()> {
        let enode = &mut self.enodes[from];
        let to = expl.to();
        let eq = Equality {
            _frame: stack.active_frame(),
            to,
            expl,
        };
        enode.equalities.try_reserve(1)?;
        enode.equalities.push(eq);
        // TODO: is ok to simply ignore the old equality, or should we also blame it later on?
        // let (new, others) = enode.equalities.split_last().unwrap();
        // if let Some(old) = others.last() {
        //     let inactive = old.frame.map(|f| !stack.stack_frames[f].active).unwrap_or_default();
        //     if inactive {
        //         return;
        //     }
        //     let is_root = matches!(old.expl, EqualityExpl::Root { .. });
        //     let root_unchanged = is_root || (self.path_to_root(old.to)[0] == self.path_to_root(new.to)[0]);
        //     if root_unchanged {
        //         return;
        //     }

        //     let is_unknown = matches!(enode.get_equality(stack).unwrap().expl, EqualityExpl::Unknown { .. });
        //     let equivalent = old.expl == enode.get_equality(stack).unwrap().expl;
        //     // let test = old.frame.is_some_and(|f| usize::from(f) == 854);
        //     if !equivalent && !is_unknown {
        //         panic!();
        //     }
        // }
        Ok(())
    }

    pub fn path_to_root(&self, from: ENodeIdx, stack: &Stack, depth: usize) -> Vec<ENodeIdx> {
        if let Some(eq) = &self.enodes[from].get_equality(stack) {
            if eq.to != from {
                let mut path = self.path_to_root(eq.to, stack, depth + 1);
                path.push(from);
                return path;
            }
        }
        let mut path = Vec::with_capacity(depth + 1);
        path.push(from);
        path
    }

    pub fn get_equalities<'a: 'b, 'b>(&'a self, from: ENodeIdx, to: ENodeIdx, stack: &'b Stack, can_mismatch: impl Fn() -> bool) -> Result<impl Iterator<Item = &'a EqualityExpl> + 'b> {
        let f_path = self.path_to_root(from, stack, 0);
        let t_path = self.path_to_root(to, stack, 0);
        let mut shared = 1;
        if f_path[0] != t_path[0] {
            // Root may not always be the same from v4.12.3 onwards if `to` is an `ite` expression. See:
            // https://github.com/Z3Prover/z3/commit/faf14012ba18d21c1fcddbdc321ac127f019fa03#diff-0a9ec50ded668e51578edc67ecfe32380336b9cbf12c5d297e2d3759a7a39847R2417-R2419
            if !can_mismatch() {
                return Err(Error::EnodeRootMismatch(from, to));
            }
            // Return an empty iterator if the roots are different.
            shared = f_path.len().max(t_path.len());
        }
        while shared < f_path.len() && shared < t_path.len() && f_path[shared] == t_path[shared] {
            shared += 1;
        }
        let all = f_path.into_iter().skip(shared).rev().chain(t_path.into_iter().skip(shared));
        Ok(all.map(|idx| &self.enodes[idx].get_equality(stack).unwrap().expl))
    }

    pub fn blame_equalities(&self, from: ENodeIdx, to: ENodeIdx, stack: &Stack, blamed: &mut Vec<BlameKind>, can_mismatch: impl Fn() -> bool) -> Result<()> {
        for eq in self.get_equalities(from, to, stack, can_mismatch)? {
            // TODO: figure out if this is all the blames we need.
            match eq {
                EqualityExpl::Root { .. } => unreachable!(),
                &EqualityExpl::Literal { eq, .. } => {
                    blamed.push(BlameKind::Equality { eq });
                }
                EqualityExpl::Congruence { arg_eqs, .. } => {
                    for (from, to) in arg_eqs.iter() {
                        fn cannot_mismatch() -> bool { false }
                        self.blame_equalities(*from, *to, stack, blamed, cannot_mismatch)?;
                    }
                }
                EqualityExpl::Theory { .. } => (),
                EqualityExpl::Axiom { .. } => (),
                EqualityExpl::Unknown { .. } => (),
            }
        }
        Ok(())
    }
}

impl std::ops::Index<ENodeIdx> for EGraph {
    type Output = ENode;
    fn index(&self, idx: ENodeIdx) -> &Self::Output {
        &self.enodes[idx]
    }
}

#[derive(Debug)]
pub struct ENode {
    frame: Option<StackIdx>,
    pub created_by: Option<InstIdx>,
    pub owner: TermIdx,
    pub z3_generation: Option<u32>,

    equalities: Vec<Equality>,
}

impl ENode {
    pub fn get_equality(&self, _stack: &Stack) -> Option<&Equality> {
        // TODO: why are we allowed to use equalities from popped stack frames?
        // self.equalities.iter().rev().find(|eq| eq.frame.map(|f| stack.stack_frames[f].active).unwrap_or(true))
        self.equalities.last()
    }
}

#[derive(Debug)]
pub struct Equality {
    _frame: Option<StackIdx>,
    pub to: ENodeIdx,
    pub expl: EqualityExpl,
}
