//! Infer integer and pointer slots only from operations with decisive shapes.
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

#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct PointerUse {
    dereferenced: bool,
    other: bool,
}

#[derive(Clone, Default, PartialEq, Eq)]
struct PointeeEvidence {
    candidate: Option<VariableType>,
    conflicting: bool,
}

impl PointeeEvidence {
    fn merge(&mut self, other: &Self) {
        if self.conflicting || other.conflicting {
            self.candidate = None;
            self.conflicting = true;
        } else if let Some(candidate) = &other.candidate {
            if self
                .candidate
                .as_ref()
                .is_some_and(|current| current != candidate)
            {
                self.candidate = None;
                self.conflicting = true;
            } else {
                self.candidate = Some(candidate.clone());
            }
        }
    }
}

#[derive(Default)]
struct Analysis {
    types: HashMap<Slot, VariableType>,
    evidence: HashMap<Slot, Evidence>,
    copies: Vec<(Slot, Slot)>,
    pointer_uses: HashMap<Slot, PointerUse>,
    derived_addresses: Vec<(Slot, Slot)>,
    pointees: HashMap<Slot, PointeeEvidence>,
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

fn width(ty: &VariableType) -> Option<usize> {
    match ty {
        VariableType::Unknown(Some(size)) if matches!(size, 1 | 2 | 4 | 8) => Some(*size),
        _ => None,
    }
}

fn pointee_width(ty: &VariableType) -> Option<usize> {
    match ty {
        VariableType::Bool => Some(1),
        VariableType::Integer(bits) | VariableType::UnsignedInteger(bits) => Some(bits / 8),
        _ => None,
    }
}

impl Analysis {
    fn width(&self, slot: Slot) -> Option<usize> {
        self.types.get(&slot).and_then(width)
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

    fn pointer_use(&mut self, slot: Slot, dereferenced: bool) {
        let uses = self.pointer_uses.entry(slot).or_default();
        uses.dereferenced |= dereferenced;
        uses.other |= !dereferenced;
    }

    // An offset must have its own integer shape. Two unknown operands of an
    // addition do not identify which one is the address base.
    fn integer_offset(&self, expr: &IRExpr, owner: SyntheticFunctionId) -> bool {
        if literal_size(expr).is_some() {
            return true;
        }
        if let Some(slot) = direct_slot(expr, owner) {
            let original = self.types.get(&slot).cloned();
            return original.is_some_and(|ty| {
                matches!(
                    self.inferred(slot, ty),
                    VariableType::Integer(_) | VariableType::UnsignedInteger(_)
                )
            });
        }
        match expr {
            IRExpr::BinOp {
                kind: IRBinOpKind::Add | IRBinOpKind::Sub | IRBinOpKind::Shl,
                lhs,
                rhs,
            } => self.integer_offset(lhs, owner) && self.integer_offset(rhs, owner),
            _ => false,
        }
    }

    fn address_base<'a>(
        &self,
        expr: &'a IRExpr,
        owner: SyntheticFunctionId,
    ) -> Option<(&'a IRExpr, &'a IRExpr)> {
        let IRExpr::BinOp {
            kind: IRBinOpKind::Add,
            lhs,
            rhs,
        } = expr
        else {
            return None;
        };
        match (
            self.integer_offset(lhs, owner),
            self.integer_offset(rhs, owner),
        ) {
            (false, true) => Some((lhs, rhs)),
            (true, false) => Some((rhs, lhs)),
            _ => None,
        }
    }

    fn pointer_address(&mut self, expr: &IRExpr, owner: SyntheticFunctionId) {
        match expr {
            IRExpr::MemoryAddress { address, .. } => self.pointer_address(address, owner),
            _ => {
                if let Some(slot) = direct_slot(expr, owner) {
                    self.pointer_use(slot, true);
                } else if let Some((base, offset)) = self.address_base(expr, owner) {
                    self.pointer_address(base, owner);
                    self.pointer_value(offset, owner);
                } else {
                    self.pointer_value(expr, owner);
                }
            }
        }
    }

    fn pointer_value(&mut self, expr: &IRExpr, owner: SyntheticFunctionId) {
        if let Some(slot) = direct_slot(expr, owner) {
            self.pointer_use(slot, false);
            return;
        }
        match expr {
            IRExpr::Deref(address) => self.pointer_address(address, owner),
            IRExpr::BinOp { lhs, rhs, .. } => {
                self.pointer_value(lhs, owner);
                self.pointer_value(rhs, owner);
            }
            IRExpr::ReplaceBytes {
                original, value, ..
            } => {
                self.pointer_value(original, owner);
                self.pointer_value(value, owner);
            }
            IRExpr::MemoryAddress { address: value, .. }
            | IRExpr::ExtractBytes { value, .. }
            | IRExpr::ZeroExtend { value, .. }
            | IRExpr::Not(value) => self.pointer_value(value, owner),
            IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_) | IRExpr::Bool(_) => {}
            IRExpr::Argument(_) | IRExpr::Variable(_) => unreachable!(),
        }
    }

    fn pointer_assignment(&mut self, dest: Slot, value: &IRExpr, owner: SyntheticFunctionId) {
        if let Some(src) = direct_slot(value, owner) {
            if self.width(dest).is_some() && self.width(dest) == self.width(src) {
                return; // Exact copies are accounted for by the copy graph.
            }
        }
        if self.width(dest) == Some(8)
            && let Some((base, offset)) = self.address_base(value, owner)
            && let Some(src) = direct_slot(base, owner)
            && self.width(src) == Some(8)
        {
            self.derived_addresses.push((dest, src));
            self.pointer_value(offset, owner);
            return;
        }
        self.pointer_value(value, owner);
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
            | IRExpr::MemoryAddress { address: inner, .. }
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
            IRExpr::Deref(address) | IRExpr::MemoryAddress { address, .. } => {
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
            IRInst::DeclareAndAssignVariable {
                variable, value, ..
            } => {
                self.assignment(Slot::Variable(*variable), value, owner);
            }
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

    fn pointer_instruction(
        &mut self,
        instr: &IRInst,
        owner: SyntheticFunctionId,
        program: &Program,
    ) {
        match instr {
            IRInst::DeclareVariable { .. } => {}
            IRInst::DeclareAndAssignVariable {
                variable, value, ..
            } => {
                self.pointer_assignment(Slot::Variable(*variable), value, owner);
            }
            IRInst::Assign { dest, src } => {
                if let Some(slot) = direct_slot(dest, owner) {
                    self.pointer_assignment(slot, src, owner);
                } else {
                    self.pointer_value(dest, owner);
                    self.pointer_value(src, owner);
                }
            }
            IRInst::AssignVariable { variable, value } => {
                self.pointer_assignment(Slot::Variable(*variable), value, owner);
            }
            IRInst::LoadVariable { address, .. } => {
                self.pointer_address(address, owner);
            }
            IRInst::StoreVariable { address, variable } => {
                self.pointer_address(address, owner);
                self.pointer_use(Slot::Variable(*variable), false);
            }
            IRInst::Return(Some(value)) | IRInst::Jump(value) => {
                self.pointer_value(value, owner);
            }
            IRInst::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.pointer_value(condition, owner);
                for instr in then_branch.iter().chain(else_branch) {
                    self.pointer_instruction(instr, owner, program);
                }
            }
            IRInst::While {
                condition, body, ..
            } => {
                match condition {
                    LoopCondition::Before { expression, .. }
                    | LoopCondition::After { expression, .. } => {
                        self.pointer_value(expression, owner)
                    }
                }
                for (_, instr) in body {
                    self.pointer_instruction(instr, owner, program);
                }
            }
            IRInst::CallSynthetic {
                function,
                arguments,
            } => {
                let callee = program.functions.get(function.id);
                for (index, argument) in arguments.iter().enumerate() {
                    if let Some(parameter) = callee.and_then(|callee| callee.parameters.get(index))
                    {
                        let dest = match parameter {
                            Parameter::Argument { ordinal, .. } => {
                                Slot::Argument(*function, *ordinal)
                            }
                            Parameter::Slot { variable, .. } => Slot::Variable(*variable),
                        };
                        self.pointer_assignment(dest, argument, owner);
                    } else {
                        self.pointer_value(argument, owner);
                    }
                }
            }
            IRInst::Return(None)
            | IRInst::Break
            | IRInst::Continue
            | IRInst::ContinueLoop(_)
            | IRInst::End => {}
        }
    }

    fn propagate_pointer_uses(&mut self) {
        // A derived address transfers pointer evidence from its dereferenced
        // result to its base. All other uses of either copy are shared.
        loop {
            let mut changed = false;
            for &(dest, src) in &self.copies {
                let left = self.pointer_uses.get(&dest).copied().unwrap_or_default();
                let right = self.pointer_uses.get(&src).copied().unwrap_or_default();
                let merged = PointerUse {
                    dereferenced: left.dereferenced || right.dereferenced,
                    other: left.other || right.other,
                };
                for slot in [dest, src] {
                    if self.pointer_uses.insert(slot, merged) != Some(merged) {
                        changed = true;
                    }
                }
            }
            for &(dest, base) in &self.derived_addresses {
                let result = self.pointer_uses.get(&dest).copied().unwrap_or_default();
                let uses = self.pointer_uses.entry(base).or_default();
                if result.dereferenced && !uses.dereferenced {
                    uses.dereferenced = true;
                    changed = true;
                }
                // A derived value used for anything other than an address
                // makes the base ambiguous as well.
                if result.other && !uses.other {
                    uses.other = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // An addition whose result is never used as an address is an ordinary
        // arithmetic use of its base. Propagate that disqualification through
        // copies and earlier derived addresses.
        for &(dest, base) in &self.derived_addresses {
            if !self
                .pointer_uses
                .get(&dest)
                .is_some_and(|uses| uses.dereferenced)
            {
                self.pointer_uses.entry(base).or_default().other = true;
            }
        }
        loop {
            let mut changed = false;
            for &(dest, src) in &self.copies {
                if self.pointer_uses.get(&dest).is_some_and(|uses| uses.other)
                    || self.pointer_uses.get(&src).is_some_and(|uses| uses.other)
                {
                    for slot in [dest, src] {
                        let uses = self.pointer_uses.entry(slot).or_default();
                        changed |= !uses.other;
                        uses.other = true;
                    }
                }
            }
            for &(dest, base) in &self.derived_addresses {
                if self.pointer_uses.get(&dest).is_some_and(|uses| uses.other) {
                    let uses = self.pointer_uses.entry(base).or_default();
                    changed |= !uses.other;
                    uses.other = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn scalar_type(&self, slot: Slot) -> Option<VariableType> {
        let original = self.types.get(&slot)?.clone();
        let inferred = self.inferred(slot, original);
        pointee_width(&inferred).map(|_| inferred)
    }

    fn record_pointee(&mut self, address: &IRExpr, ty: VariableType, owner: SyntheticFunctionId) {
        let address = match address {
            IRExpr::MemoryAddress { address, size } => {
                if size.is_some_and(|size| Some(size) != pointee_width(&ty)) {
                    return;
                }
                address.as_ref()
            }
            _ => address,
        };
        if let Some(slot) = direct_slot(address, owner)
            && self.width(slot) == Some(8)
        {
            self.pointees
                .entry(slot)
                .or_default()
                .merge(&PointeeEvidence {
                    candidate: Some(ty),
                    conflicting: false,
                });
        }
    }

    fn pointee_assignment(&mut self, dest: Slot, value: &IRExpr, owner: SyntheticFunctionId) {
        if let IRExpr::Deref(address) = value
            && let Some(ty) = self.scalar_type(dest)
        {
            self.record_pointee(address, ty, owner);
        }
    }

    fn pointee_instruction(
        &mut self,
        instr: &IRInst,
        owner: SyntheticFunctionId,
        program: &Program,
    ) {
        match instr {
            IRInst::DeclareAndAssignVariable {
                variable, value, ..
            }
            | IRInst::AssignVariable { variable, value } => {
                self.pointee_assignment(Slot::Variable(*variable), value, owner);
            }
            IRInst::Assign { dest, src } => {
                if let Some(slot) = direct_slot(dest, owner) {
                    self.pointee_assignment(slot, src, owner);
                }
                if let IRExpr::Deref(address) = dest
                    && let Some(src) = direct_slot(src, owner)
                    && let Some(ty) = self.scalar_type(src)
                {
                    self.record_pointee(address, ty, owner);
                }
            }
            IRInst::LoadVariable { variable, address } => {
                if let Some(ty) = self.scalar_type(Slot::Variable(*variable)) {
                    self.record_pointee(address, ty, owner);
                }
            }
            IRInst::StoreVariable { address, variable } => {
                if let Some(ty) = self.scalar_type(Slot::Variable(*variable)) {
                    self.record_pointee(address, ty, owner);
                }
            }
            IRInst::CallSynthetic {
                function,
                arguments,
            } => {
                if let Some(callee) = program.functions.get(function.id) {
                    for (parameter, argument) in callee.parameters.iter().zip(arguments) {
                        let dest = match parameter {
                            Parameter::Argument { ordinal, .. } => {
                                Slot::Argument(*function, *ordinal)
                            }
                            Parameter::Slot { variable, .. } => Slot::Variable(*variable),
                        };
                        self.pointee_assignment(dest, argument, owner);
                    }
                }
            }
            IRInst::If {
                then_branch,
                else_branch,
                ..
            } => {
                for instr in then_branch.iter().chain(else_branch) {
                    self.pointee_instruction(instr, owner, program);
                }
            }
            IRInst::While { body, .. } => {
                for (_, instr) in body {
                    self.pointee_instruction(instr, owner, program);
                }
            }
            IRInst::DeclareVariable { .. }
            | IRInst::Return(_)
            | IRInst::Break
            | IRInst::Continue
            | IRInst::ContinueLoop(_)
            | IRInst::Jump(_)
            | IRInst::End => {}
        }
    }

    fn propagate_pointees(&mut self) {
        loop {
            let mut changed = false;
            for &(dest, src) in &self.copies {
                let mut merged = self.pointees.get(&dest).cloned().unwrap_or_default();
                merged.merge(&self.pointees.get(&src).cloned().unwrap_or_default());
                for slot in [dest, src] {
                    if self.pointees.get(&slot) != Some(&merged) {
                        self.pointees.insert(slot, merged.clone());
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn inferred_pointer(&self, slot: Slot, original: VariableType) -> VariableType {
        if original != VariableType::Unknown(Some(8)) {
            return original;
        }
        let uses = self.pointer_uses.get(&slot).copied().unwrap_or_default();
        let integer = self
            .evidence
            .get(&slot)
            .is_some_and(|evidence| evidence.integer);
        if uses.dereferenced && !uses.other && !integer {
            self.pointees
                .get(&slot)
                .and_then(|evidence| evidence.candidate.clone())
                .map_or(VariableType::UnknownPointer, |ty| {
                    VariableType::Pointer(Box::new(ty))
                })
        } else {
            original
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
        let Some(size) = width(&original) else {
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
        IRInst::DeclareVariable { variable, ty }
        | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
            let slot = Slot::Variable(*variable);
            *ty = analysis.inferred_pointer(slot, analysis.inferred(slot, ty.clone()));
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
        IRInst::DeclareVariable { variable, ty }
        | IRInst::DeclareAndAssignVariable { variable, ty, .. } => {
            analysis.types.insert(Slot::Variable(*variable), ty.clone());
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
                    analysis
                        .types
                        .insert(Slot::Argument(owner, *ordinal), ty.clone());
                }
                Parameter::Slot { variable, ty } => {
                    analysis.types.insert(Slot::Variable(*variable), ty.clone());
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
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for (_, instr) in &function.body {
            analysis.pointer_instruction(instr, owner, program);
        }
    }
    analysis.propagate_pointer_uses();
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for (_, instr) in &function.body {
            analysis.pointee_instruction(instr, owner, program);
        }
    }
    analysis.propagate_pointees();
    for (index, function) in program.functions.iter_mut().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for parameter in &mut function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    let slot = Slot::Argument(owner, *ordinal);
                    *ty = analysis.inferred_pointer(slot, analysis.inferred(slot, ty.clone()));
                }
                Parameter::Slot { variable, ty } => {
                    let slot = Slot::Variable(*variable);
                    *ty = analysis.inferred_pointer(slot, analysis.inferred(slot, ty.clone()));
                }
            }
        }
        for (_, instr) in &mut function.body {
            retype(instr, &analysis);
        }
    }
}
