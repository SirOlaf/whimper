pub mod ir;

use std::collections::{HashMap, HashSet};

use iced_x86::Register;

use crate::irt0::ir::{
    IRBinOpKind, IRExpr, IRInst as IRT0Inst, NativeFlag, Program as IRT0Program,
};

use self::ir::{IRInst, Program, SyntheticFunction, SyntheticFunctionId};

fn jump_target(expr: &IRExpr, offset: usize) -> Option<usize> {
    match expr {
        IRExpr::CU64(value) => usize::try_from(*value).ok(),
        IRExpr::CU32(value) => usize::try_from(*value).ok(),
        IRExpr::Reg(Register::RIP) => Some(offset),
        IRExpr::BinOp {
            kind: IRBinOpKind::Add,
            lhs,
            rhs,
        } => jump_target(lhs, offset)?.checked_add(jump_target(rhs, offset)?),
        _ => None,
    }
}

struct SyntheticFunctionBuilder<'a> {
    source: &'a IRT0Program,
    jump_entries: HashSet<usize>,
    by_start: HashMap<usize, SyntheticFunctionId>,
    functions: Vec<SyntheticFunction>,
}

impl SyntheticFunctionBuilder<'_> {
    // The tier 0 program has one or more operations per source address. A jump
    // into an omitted NOP starts at the first surviving operation after it.
    fn index_at(&self, offset: usize) -> Option<usize> {
        let index = self
            .source
            .partition_point(|(address, _)| *address < offset);
        (index < self.source.len()).then_some(index)
    }

    fn local_target(&self, expr: &IRExpr, offset: usize) -> Option<usize> {
        let target = jump_target(expr, offset)?;
        if target < self.source.first()?.0 || target > self.source.last()?.0 {
            return None;
        }
        self.index_at(target)
    }

    fn target(&mut self, expr: &IRExpr, offset: usize) -> IRInst {
        match self.local_target(expr, offset) {
            Some(index) => IRInst::CallSynthetic {
                function: self.function(index),
            },
            None => IRInst::Jump(expr.clone()),
        }
    }

    fn fallthrough(&mut self, index: usize) -> IRInst {
        if index < self.source.len() {
            IRInst::CallSynthetic {
                function: self.function(index),
            }
        } else {
            IRInst::End
        }
    }

    fn function(&mut self, start: usize) -> SyntheticFunctionId {
        if let Some(reference) = self.by_start.get(&start) {
            return *reference;
        }

        // Reserve the function before following its edges. A backward jump
        // can then call a function that is still being constructed.
        let reference = SyntheticFunctionId {
            id: self.functions.len(),
        };
        self.by_start.insert(start, reference);
        self.functions.push(SyntheticFunction {
            entry_offset: self.source[start].0,
            external_flags: HashSet::new(),
            body: Vec::new(),
        });

        let mut body: Vec<(usize, IRInst)> = Vec::new();
        let mut index = start;
        while index < self.source.len() {
            let (offset, instr) = &self.source[index];
            let offset = *offset;
            let instr = instr.clone();

            // Split before any shared entry. Without this boundary, the same
            // source instructions would also be copied into the predecessor.
            if index != start
                && (self.jump_entries.contains(&index) || self.by_start.contains_key(&index))
            {
                let previous_offset = body.last().unwrap().0;
                body.push((previous_offset, self.fallthrough(index)));
                break;
            }

            match instr {
                IRT0Inst::If(condition, inner) => {
                    let IRT0Inst::Jmp(target) = inner.as_ref() else {
                        panic!("tier 1 expects a jump inside a tier 0 conditional");
                    };
                    let then_branch = self.target(target, offset);
                    let else_branch = self.fallthrough(index + 1);
                    body.push((
                        offset,
                        IRInst::If {
                            condition,
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        },
                    ));
                    break;
                }
                IRT0Inst::Jmp(target) => {
                    let target = self.target(&target, offset);
                    body.push((offset, target));
                    break;
                }
                IRT0Inst::Ret(_) => {
                    body.push((offset, IRInst::Linear(instr)));
                    break;
                }
                _ => body.push((offset, IRInst::Linear(instr))),
            }
            index += 1;
        }

        self.functions[reference.id].external_flags = external_flags(&body);
        self.functions[reference.id].body = body;
        reference
    }
}

fn read_flags(expr: &IRExpr, defined: &HashSet<NativeFlag>, external: &mut HashSet<NativeFlag>) {
    match expr {
        IRExpr::BinOp { lhs, rhs, .. } => {
            read_flags(lhs, defined, external);
            read_flags(rhs, defined, external);
        }
        IRExpr::Deref(inner) => read_flags(inner, defined, external),
        IRExpr::Flag(flag) if !defined.contains(flag) => {
            external.insert(flag.clone());
        }
        _ => {}
    }
}

fn external_flags(body: &[(usize, IRInst)]) -> HashSet<NativeFlag> {
    let mut defined = HashSet::new();
    let mut external = HashSet::new();
    for (_, instr) in body {
        match instr {
            IRInst::Linear(IRT0Inst::SetFlagsFrom(flags, expr)) => {
                read_flags(expr, &defined, &mut external);
                defined.extend(flags.iter().cloned());
            }
            IRInst::Linear(IRT0Inst::ClearFlags(flags)) => {
                defined.extend(flags.iter().cloned());
            }
            IRInst::Linear(IRT0Inst::Asgn { dest, src }) => {
                read_flags(dest, &defined, &mut external);
                read_flags(src, &defined, &mut external);
            }
            IRInst::Linear(IRT0Inst::Ret(Some(expr)))
            | IRInst::If {
                condition: expr, ..
            } => {
                read_flags(expr, &defined, &mut external);
            }
            _ => {}
        }
    }
    external
}

pub fn lift(source: &IRT0Program) -> Program {
    if source.is_empty() {
        return Program {
            entry: None,
            functions: Vec::new(),
        };
    }

    let mut builder = SyntheticFunctionBuilder {
        source,
        jump_entries: HashSet::new(),
        by_start: HashMap::new(),
        functions: Vec::new(),
    };

    for (offset, instr) in source {
        let target = match instr {
            IRT0Inst::Jmp(target) => Some(target),
            IRT0Inst::If(_, inner) => match inner.as_ref() {
                IRT0Inst::Jmp(target) => Some(target),
                _ => None,
            },
            _ => None,
        };
        if let Some(index) = target.and_then(|expr| builder.local_target(expr, *offset)) {
            builder.jump_entries.insert(index);
        }
    }

    let entry = builder.function(0);
    Program {
        entry: Some(entry),
        functions: builder.functions,
    }
}
