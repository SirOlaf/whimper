//! Infer integer slots only from operations whose shape supplies integer evidence.
//! Copies and synthetic calls carry that evidence across slots of equal width.

use std::collections::HashMap;

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, Parameter, Program, SyntheticFunctionId,
    VariableId, VariableType,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Slot {
    Variable(VariableId),
    Argument(SyntheticFunctionId, usize),
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Evidence {
    integer: bool,
    unsigned: bool,
    address: bool,
}

#[derive(Default)]
struct Analysis {
    types: HashMap<Slot, VariableType>,
    evidence: HashMap<Slot, Evidence>,
    copies: Vec<(Slot, Slot)>,
}

fn direct_slot(expr: &IRExpr, owner: SyntheticFunctionId) -> Option<Slot> {
    match expr {
        IRExpr::Variable(variable) => Some(Slot::Variable(*variable)),
        IRExpr::Argument(ordinal) => Some(Slot::Argument(owner, *ordinal)),
        _ => None,
    }
}

fn literal_size(expr: &IRExpr) -> Option<usize> {
    match expr {
        IRExpr::CU8(_) => Some(1),
        IRExpr::CU32(_) => Some(4),
        IRExpr::CU64(_) => Some(8),
        _ => None,
    }
}

fn width(ty: VariableType) -> Option<usize> {
    match ty {
        VariableType::Unknown(Some(size)) if matches!(size, 1 | 2 | 4 | 8) => Some(size),
        _ => None,
    }
}

impl Analysis {
    fn width(&self, slot: Slot) -> Option<usize> {
        self.types.get(&slot).copied().and_then(width)
    }

    fn integer(&mut self, slot: Slot, unsigned: bool) {
        if self.width(slot).is_some() {
            let evidence = self.evidence.entry(slot).or_default();
            evidence.integer = true;
            evidence.unsigned |= unsigned;
        }
    }

    fn copy(&mut self, dest: Slot, src: Slot) {
        if self.width(dest).is_some() && self.width(dest) == self.width(src) {
            self.copies.push((dest, src));
        }
    }

    fn address(&mut self, expr: &IRExpr, owner: SyntheticFunctionId) {
        if let Some(slot) = direct_slot(expr, owner) {
            self.evidence.entry(slot).or_default().address = true;
            return;
        }
        match expr {
            IRExpr::BinOp { lhs, rhs, .. } => {
                self.address(lhs, owner);
                self.address(rhs, owner);
            }
            IRExpr::ReplaceBytes {
                original, value, ..
            } => {
                self.address(original, owner);
                self.address(value, owner);
            }
            IRExpr::Deref(inner)
            | IRExpr::CastUnknownPtr { address: inner, .. }
            | IRExpr::ExtractBytes { value: inner, .. }
            | IRExpr::ZeroExtend { value: inner, .. }
            | IRExpr::Not(inner) => self.address(inner, owner),
            IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_) | IRExpr::Bool(_) => {}
            IRExpr::Argument(_) | IRExpr::Variable(_) => unreachable!(),
        }
    }

    fn expression(&mut self, expr: &IRExpr, owner: SyntheticFunctionId) {
        match expr {
            IRExpr::BinOp { kind, lhs, rhs } => {
                match kind {
                    IRBinOpKind::Shl | IRBinOpKind::UnsignedLt => {
                        let unsigned = *kind == IRBinOpKind::UnsignedLt;
                        for operand in [lhs.as_ref(), rhs.as_ref()] {
                            if let Some(slot) = direct_slot(operand, owner) {
                                self.integer(slot, unsigned);
                            }
                        }
                    }
                    IRBinOpKind::Eq => {
                        for (operand, literal) in [(lhs.as_ref(), rhs.as_ref()), (rhs, lhs)] {
                            if let (Some(slot), Some(size)) =
                                (direct_slot(operand, owner), literal_size(literal))
                            {
                                if self.width(slot) == Some(size) {
                                    self.integer(slot, false);
                                }
                            }
                        }
                    }
                    IRBinOpKind::Add | IRBinOpKind::Sub | IRBinOpKind::And | IRBinOpKind::Or => {}
                }
                self.expression(lhs, owner);
                self.expression(rhs, owner);
            }
            IRExpr::Deref(address) | IRExpr::CastUnknownPtr { address, .. } => {
                self.address(address, owner);
                self.expression(address, owner);
            }
            IRExpr::ReplaceBytes {
                original, value, ..
            } => {
                self.expression(original, owner);
                self.expression(value, owner);
            }
            IRExpr::ExtractBytes { value, .. }
            | IRExpr::ZeroExtend { value, .. }
            | IRExpr::Not(value) => self.expression(value, owner),
            IRExpr::Argument(_)
            | IRExpr::Variable(_)
            | IRExpr::CU8(_)
            | IRExpr::CU32(_)
            | IRExpr::CU64(_)
            | IRExpr::Bool(_) => {}
        }
    }

    fn assignment(&mut self, dest: Slot, value: &IRExpr, owner: SyntheticFunctionId) {
        if let Some(src) = direct_slot(value, owner) {
            self.copy(dest, src);
        }
        if matches!(
            value,
            IRExpr::BinOp {
                kind: IRBinOpKind::Shl,
                ..
            }
        ) {
            self.integer(dest, false);
        }
        self.expression(value, owner);
    }

    fn instruction(&mut self, instr: &IRInst, owner: SyntheticFunctionId) {
        match instr {
            IRInst::DeclareVariable { .. } => {}
            IRInst::Assign { dest, src } => {
                if let Some(slot) = direct_slot(dest, owner) {
                    self.assignment(slot, src, owner);
                } else {
                    self.expression(dest, owner);
                    self.expression(src, owner);
                }
            }
            IRInst::AssignVariable { variable, value } => {
                self.assignment(Slot::Variable(*variable), value, owner);
            }
            IRInst::LoadVariable { address, .. } | IRInst::StoreVariable { address, .. } => {
                self.address(address, owner);
                self.expression(address, owner);
            }
            IRInst::Return(Some(value)) => {
                self.expression(value, owner);
            }
            IRInst::Jump(target) => {
                self.address(target, owner);
                self.expression(target, owner);
            }
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expression(condition, owner);
                for instr in then_branch.iter().chain(else_branch) {
                    self.instruction(instr, owner);
                }
            }
            IRInst::While {
                condition, body, ..
            } => {
                match condition {
                    LoopCondition::Before { expression, .. }
                    | LoopCondition::After { expression, .. } => self.expression(expression, owner),
                }
                for (_, instr) in body {
                    self.instruction(instr, owner);
                }
            }
            IRInst::CallSynthetic { arguments, .. } => {
                for argument in arguments {
                    self.expression(argument, owner);
                }
            }
            IRInst::Return(None)
            | IRInst::Break
            | IRInst::Continue
            | IRInst::ContinueLoop(_)
            | IRInst::End => {}
        }
    }

    fn propagate(&mut self) {
        // Exact copies have the same bit pattern. A pointer-shaped member
        // makes the whole copy group ineligible for integer retyping.
        loop {
            let mut changed = false;
            for &(dest, src) in &self.copies {
                let left = self.evidence.get(&dest).copied().unwrap_or_default();
                let right = self.evidence.get(&src).copied().unwrap_or_default();
                let merged = Evidence {
                    integer: left.integer || right.integer,
                    unsigned: left.unsigned || right.unsigned,
                    address: left.address || right.address,
                };
                for slot in [dest, src] {
                    if self.evidence.insert(slot, merged) != Some(merged) {
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn inferred(&self, slot: Slot, original: VariableType) -> VariableType {
        let Some(size) = width(original) else {
            return original;
        };
        let evidence = self.evidence.get(&slot).copied().unwrap_or_default();
        if !evidence.integer || evidence.address {
            return original;
        }
        let bits = size * 8;
        if evidence.unsigned {
            VariableType::UnsignedInteger(bits)
        } else {
            // Tier 5 uses i<N> for integer-shaped values without a signed
            // comparison. A later tier can refine their signedness.
            VariableType::Integer(bits)
        }
    }
}

fn retype(instr: &mut IRInst, analysis: &Analysis) {
    match instr {
        IRInst::DeclareVariable { variable, ty } => {
            *ty = analysis.inferred(Slot::Variable(*variable), *ty);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter_mut().chain(else_branch) {
                retype(instr, analysis);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                retype(instr, analysis);
            }
        }
        _ => {}
    }
}

fn declarations(instr: &IRInst, analysis: &mut Analysis) {
    match instr {
        IRInst::DeclareVariable { variable, ty } => {
            analysis.types.insert(Slot::Variable(*variable), *ty);
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                declarations(instr, analysis);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                declarations(instr, analysis);
            }
        }
        _ => {}
    }
}

fn calls(instr: &IRInst, owner: SyntheticFunctionId, program: &Program, analysis: &mut Analysis) {
    match instr {
        IRInst::CallSynthetic {
            function,
            arguments,
        } => {
            if let Some(callee) = program.functions.get(function.id) {
                for (parameter, argument) in callee.parameters.iter().zip(arguments) {
                    let Some(src) = direct_slot(argument, owner) else {
                        continue;
                    };
                    let dest = match parameter {
                        Parameter::Argument { ordinal, .. } => Slot::Argument(*function, *ordinal),
                        Parameter::Slot { variable, .. } => Slot::Variable(*variable),
                    };
                    analysis.copy(dest, src);
                }
            }
        }
        IRInst::If {
            then_branch,
            else_branch,
            ..
        } => {
            for instr in then_branch.iter().chain(else_branch) {
                calls(instr, owner, program, analysis);
            }
        }
        IRInst::While { body, .. } => {
            for (_, instr) in body {
                calls(instr, owner, program, analysis);
            }
        }
        _ => {}
    }
}

pub fn run(program: &mut Program) {
    let mut analysis = Analysis::default();
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for parameter in &function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    analysis.types.insert(Slot::Argument(owner, *ordinal), *ty);
                }
                Parameter::Slot { variable, ty } => {
                    analysis.types.insert(Slot::Variable(*variable), *ty);
                }
            }
        }
    }
    // Collect declarations before evidence, since uses can precede the
    // declaration in structured loop bodies.
    for function in &program.functions {
        for (_, instr) in &function.body {
            declarations(instr, &mut analysis);
        }
    }
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for (_, instr) in &function.body {
            analysis.instruction(instr, owner);
        }
    }
    // A synthetic parameter carries the caller's value without conversion.
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for (_, instr) in &function.body {
            calls(instr, owner, program, &mut analysis);
        }
    }
    analysis.propagate();
    for (index, function) in program.functions.iter_mut().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for parameter in &mut function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    *ty = analysis.inferred(Slot::Argument(owner, *ordinal), *ty);
                }
                Parameter::Slot { variable, ty } => {
                    *ty = analysis.inferred(Slot::Variable(*variable), *ty);
                }
            }
        }
        for (_, instr) in &mut function.body {
            retype(instr, &analysis);
        }
    }
}
