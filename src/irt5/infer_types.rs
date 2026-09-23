//! Infer integer, pointer, and struct slots from decisive access shapes.
//! Copies and synthetic calls carry that evidence across slots of equal width.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::ir::{
    IRBinOpKind, IRExpr, IRInst, LoopCondition, Parameter, Program, StructDefinition, StructField,
    StructId, SyntheticFunctionId, VariableId, VariableType, field_address,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Slot {
    Variable(VariableId),
    Argument(SyntheticFunctionId, usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct FieldLink {
    value: Slot,
    base: Slot,
    offset: usize,
    size: Option<usize>,
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
    indexed: bool,
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
            match self.candidate.as_ref() {
                Some(VariableType::UnknownPointer)
                    if matches!(candidate, VariableType::Pointer(_)) =>
                {
                    self.candidate = Some(candidate.clone());
                }
                Some(VariableType::Pointer(_)) if *candidate == VariableType::UnknownPointer => {}
                Some(current) if current != candidate => {
                    self.candidate = None;
                    self.conflicting = true;
                }
                None => self.candidate = Some(candidate.clone()),
                _ => {}
            }
        }
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
struct FieldEvidence {
    size: Option<usize>,
    size_conflict: bool,
    candidate: Option<VariableType>,
    type_conflict: bool,
}

impl FieldEvidence {
    fn merge(&mut self, other: &Self) {
        if self.size_conflict || other.size_conflict {
            self.size = None;
            self.size_conflict = true;
        } else if let Some(size) = other.size {
            if self.size.is_some_and(|current| current != size) {
                self.size = None;
                self.size_conflict = true;
            } else {
                self.size = Some(size);
            }
        }
        if self.type_conflict || other.type_conflict {
            self.candidate = None;
            self.type_conflict = true;
        } else if let Some(candidate) = &other.candidate {
            match self.candidate.as_ref() {
                Some(VariableType::UnknownPointer)
                    if matches!(candidate, VariableType::Pointer(_)) =>
                {
                    self.candidate = Some(candidate.clone());
                }
                Some(VariableType::Pointer(_)) if *candidate == VariableType::UnknownPointer => {}
                Some(current) if current != candidate => {
                    self.candidate = None;
                    self.type_conflict = true;
                }
                None => self.candidate = Some(candidate.clone()),
                _ => {}
            }
        }
    }

    fn ty(&self) -> VariableType {
        if !self.size_conflict && !self.type_conflict {
            if let Some(candidate) = &self.candidate {
                return candidate.clone();
            }
        }
        VariableType::Unknown(self.size)
    }
}

#[derive(Default)]
struct Analysis {
    types: HashMap<Slot, VariableType>,
    evidence: HashMap<Slot, Evidence>,
    copies: Vec<(Slot, Slot)>,
    pointer_uses: HashMap<Slot, PointerUse>,
    derived_addresses: Vec<(Slot, Slot, Option<usize>)>,
    pointees: HashMap<Slot, PointeeEvidence>,
    fields: HashMap<Slot, BTreeMap<usize, FieldEvidence>>,
    field_links: HashSet<FieldLink>,
    field_slot_types: HashMap<Slot, PointeeEvidence>,
    struct_ids: HashMap<Slot, StructId>,
    struct_representatives: Vec<Slot>,
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

fn value_width(ty: &VariableType) -> Option<usize> {
    match ty {
        VariableType::Pointer(_) | VariableType::UnknownPointer => Some(8),
        VariableType::Unknown(size) => *size,
        _ => pointee_width(ty),
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
            IRExpr::Convert { .. } => true,
            IRExpr::BinOp {
                kind: IRBinOpKind::Add | IRBinOpKind::Sub | IRBinOpKind::Mul | IRBinOpKind::Shl,
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
        if let Some((base, offset)) = field_address(expr)
            && let Some(slot) = direct_slot(base, owner)
            && self.width(slot) == Some(8)
        {
            let size = match expr {
                IRExpr::MemoryAddress { size, .. } => *size,
                _ => None,
            };
            self.fields
                .entry(slot)
                .or_default()
                .entry(offset)
                .or_default()
                .merge(&FieldEvidence {
                    size,
                    ..FieldEvidence::default()
                });
        }
        self.pointer_address_uses(expr, owner);
    }

    fn pointer_address_uses(&mut self, expr: &IRExpr, owner: SyntheticFunctionId) {
        match expr {
            IRExpr::MemoryAddress { address, .. } => self.pointer_address_uses(address, owner),
            _ => {
                if let Some(slot) = direct_slot(expr, owner) {
                    self.pointer_use(slot, true);
                } else if let Some((base, offset)) = self.address_base(expr, owner) {
                    if literal_size(offset).is_none()
                        && let Some(slot) = direct_slot(base, owner)
                    {
                        self.pointer_uses.entry(slot).or_default().indexed = true;
                    }
                    self.pointer_address_uses(base, owner);
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
            IRExpr::MemoryAddress { address: value, .. }
            | IRExpr::Convert { value, .. }
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
            self.derived_addresses.push((
                dest,
                src,
                field_address(value).map(|(_, offset)| offset),
            ));
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
            IRExpr::Deref(inner)
            | IRExpr::MemoryAddress { address: inner, .. }
            | IRExpr::Not(inner) => self.address(inner, owner),
            // Conversions in addresses produce numeric byte offsets. Their
            // input slots are not themselves pointers.
            IRExpr::Convert { .. } => self.expression(expr, owner),
            IRExpr::CU8(_) | IRExpr::CU32(_) | IRExpr::CU64(_) | IRExpr::Bool(_) => {}
            IRExpr::Argument(_) | IRExpr::Variable(_) => unreachable!(),
        }
    }

    fn expression(&mut self, expr: &IRExpr, owner: SyntheticFunctionId) {
        match expr {
            IRExpr::BinOp { kind, lhs, rhs } => {
                match kind {
                    IRBinOpKind::Mul
                    | IRBinOpKind::Shl
                    | IRBinOpKind::Shr
                    | IRBinOpKind::BitOr
                    | IRBinOpKind::SignedGt
                    | IRBinOpKind::UnsignedLt
                    | IRBinOpKind::UnsignedGe => {
                        let unsigned =
                            matches!(kind, IRBinOpKind::UnsignedLt | IRBinOpKind::UnsignedGe);
                        for operand in [lhs.as_ref(), rhs.as_ref()] {
                            if let Some(slot) = direct_slot(operand, owner) {
                                self.integer(slot, unsigned);
                            }
                        }
                    }
                    IRBinOpKind::Eq | IRBinOpKind::Ne => {
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
            IRExpr::Convert { value, source, .. } => {
                if let Some(slot) = direct_slot(value, owner) {
                    self.integer(slot, !source.signed);
                }
                self.expression(value, owner);
            }
            IRExpr::Not(value) => self.expression(value, owner),
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
                kind: IRBinOpKind::Mul | IRBinOpKind::Shl,
                ..
            } | IRExpr::Convert { .. }
        ) {
            self.integer(
                dest,
                matches!(value, IRExpr::Convert { target, .. } if !target.signed),
            );
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
                    indexed: left.indexed || right.indexed,
                    other: left.other || right.other,
                };
                for slot in [dest, src] {
                    if self.pointer_uses.insert(slot, merged) != Some(merged) {
                        changed = true;
                    }
                }
            }
            for &(dest, base, _) in &self.derived_addresses {
                let result = self.pointer_uses.get(&dest).copied().unwrap_or_default();
                let uses = self.pointer_uses.entry(base).or_default();
                if result.indexed && !uses.indexed {
                    uses.indexed = true;
                    changed = true;
                }
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
        for &(dest, base, _) in &self.derived_addresses {
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
            for &(dest, base, _) in &self.derived_addresses {
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

    fn known_type(&self, slot: Slot) -> Option<VariableType> {
        let original = self.types.get(&slot)?.clone();
        let inferred = self.inferred(slot, self.inferred_pointer(slot, original));
        match inferred {
            VariableType::Bool
            | VariableType::Integer(_)
            | VariableType::UnsignedInteger(_)
            | VariableType::UnknownPointer
            | VariableType::Pointer(_) => Some(inferred),
            _ => None,
        }
    }

    fn record_field_type(
        &mut self,
        address: &IRExpr,
        ty: VariableType,
        owner: SyntheticFunctionId,
    ) {
        let Some((base, offset)) = field_address(address) else {
            return;
        };
        let Some(slot) = direct_slot(base, owner) else {
            return;
        };
        let Some(size) = value_width(&ty) else {
            return;
        };
        if let IRExpr::MemoryAddress {
            size: Some(access_size),
            ..
        } = address
            && *access_size != size
        {
            return;
        }
        if self.width(slot) == Some(8) {
            self.fields
                .entry(slot)
                .or_default()
                .entry(offset)
                .or_default()
                .merge(&FieldEvidence {
                    size: Some(size),
                    candidate: Some(ty),
                    ..FieldEvidence::default()
                });
        }
    }

    fn link_field(&mut self, value: Slot, address: &IRExpr, owner: SyntheticFunctionId) {
        let Some((base, offset)) = field_address(address) else {
            return;
        };
        let Some(base) = direct_slot(base, owner) else {
            return;
        };
        if self.width(base) == Some(8) {
            let size = match address {
                IRExpr::MemoryAddress { size, .. } => *size,
                _ => None,
            };
            self.field_links.insert(FieldLink {
                value,
                base,
                offset,
                size,
            });
        }
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
        if let IRExpr::Deref(address) = value {
            self.link_field(dest, address, owner);
            if let Some(ty) = self.known_type(dest) {
                if pointee_width(&ty).is_some() {
                    self.record_pointee(address, ty.clone(), owner);
                }
                self.record_field_type(address, ty, owner);
            }
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
                {
                    self.link_field(src, address, owner);
                    if let Some(ty) = self.known_type(src) {
                        if pointee_width(&ty).is_some() {
                            self.record_pointee(address, ty.clone(), owner);
                        }
                        self.record_field_type(address, ty, owner);
                    }
                }
            }
            IRInst::LoadVariable { variable, address } => {
                self.link_field(Slot::Variable(*variable), address, owner);
                if let Some(ty) = self.known_type(Slot::Variable(*variable)) {
                    if pointee_width(&ty).is_some() {
                        self.record_pointee(address, ty.clone(), owner);
                    }
                    self.record_field_type(address, ty, owner);
                }
            }
            IRInst::StoreVariable { address, variable } => {
                self.link_field(Slot::Variable(*variable), address, owner);
                if let Some(ty) = self.known_type(Slot::Variable(*variable)) {
                    if pointee_width(&ty).is_some() {
                        self.record_pointee(address, ty.clone(), owner);
                    }
                    self.record_field_type(address, ty, owner);
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

    fn propagate_fields(&mut self) {
        loop {
            let mut changed = false;
            for &(dest, src) in &self.copies {
                let mut merged = self.fields.get(&dest).cloned().unwrap_or_default();
                for (&offset, evidence) in self.fields.get(&src).into_iter().flatten() {
                    merged.entry(offset).or_default().merge(evidence);
                }
                for slot in [dest, src] {
                    if self.fields.get(&slot) != Some(&merged) {
                        self.fields.insert(slot, merged.clone());
                        changed = true;
                    }
                }
            }
            for &(dest, base, displacement) in &self.derived_addresses {
                let Some(displacement) = displacement else {
                    continue;
                };
                if let Some(fields) = self.fields.get(&dest).cloned() {
                    let base_fields = self.fields.entry(base).or_default();
                    for (offset, evidence) in fields {
                        if let Some(offset) = displacement.checked_add(offset) {
                            let field = base_fields.entry(offset).or_default();
                            let previous = field.clone();
                            field.merge(&evidence);
                            changed |= *field != previous;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn assign_struct_ids(&mut self, first_id: usize) {
        let mut slots = self
            .fields
            .iter()
            .filter_map(|(&slot, fields)| (fields.len() > 1).then_some(slot))
            .collect::<Vec<_>>();
        slots.sort_by_key(|slot| match slot {
            Slot::Argument(owner, ordinal) => (owner.id, 0, *ordinal),
            Slot::Variable(variable) => (variable.owner.id, 1, variable.id),
        });
        for slot in slots {
            // Fixed displacements alongside a dynamic index describe array
            // elements; they do not establish a closed struct layout.
            if self
                .pointer_uses
                .get(&slot)
                .is_some_and(|uses| uses.indexed)
                || self.struct_ids.contains_key(&slot)
            {
                continue;
            }
            let id = StructId {
                id: first_id + self.struct_representatives.len(),
            };
            self.struct_representatives.push(slot);
            let mut pending = vec![slot];
            while let Some(current) = pending.pop() {
                if !self
                    .fields
                    .get(&current)
                    .is_some_and(|fields| fields.len() > 1)
                    || self
                        .pointer_uses
                        .get(&current)
                        .is_some_and(|uses| uses.indexed)
                    || self.struct_ids.contains_key(&current)
                {
                    continue;
                }
                self.struct_ids.insert(current, id);
                for &(dest, src) in &self.copies {
                    if dest == current && !self.struct_ids.contains_key(&src) {
                        pending.push(src);
                    } else if src == current && !self.struct_ids.contains_key(&dest) {
                        pending.push(dest);
                    }
                }
            }
        }
    }

    fn struct_definitions(&self, existing: &[StructDefinition]) -> Vec<StructDefinition> {
        let mut names = existing
            .iter()
            .map(|definition| definition.name.clone())
            .collect::<HashSet<_>>();
        let mut next_name = 0;
        self.struct_representatives
            .iter()
            .map(|slot| {
                let name = loop {
                    let candidate = format!("AStruct{next_name}");
                    next_name += 1;
                    if names.insert(candidate.clone()) {
                        break candidate;
                    }
                };
                let fields = self.fields[slot]
                    .iter()
                    .map(|(&offset, evidence)| StructField {
                        offset,
                        ty: evidence.ty(),
                    })
                    .collect();
                StructDefinition { name, fields }
            })
            .collect()
    }

    fn propagate_field_types_to_slots(&mut self) {
        for link in &self.field_links {
            let Some(field) = self
                .fields
                .get(&link.base)
                .and_then(|fields| fields.get(&link.offset))
            else {
                continue;
            };
            let ty = field.ty();
            let Some(size) = value_width(&ty) else {
                continue;
            };
            if self.width(link.value) != Some(size)
                || link.size.is_some_and(|access_size| access_size != size)
            {
                continue;
            }
            self.field_slot_types
                .entry(link.value)
                .or_default()
                .merge(&PointeeEvidence {
                    candidate: Some(ty),
                    conflicting: false,
                });
        }
        loop {
            let mut changed = false;
            for &(dest, src) in &self.copies {
                let mut merged = self
                    .field_slot_types
                    .get(&dest)
                    .cloned()
                    .unwrap_or_default();
                merged.merge(&self.field_slot_types.get(&src).cloned().unwrap_or_default());
                for slot in [dest, src] {
                    if self.field_slot_types.get(&slot) != Some(&merged) {
                        self.field_slot_types.insert(slot, merged.clone());
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn inferred_type(&self, slot: Slot, original: VariableType) -> VariableType {
        let inferred = self.inferred(slot, self.inferred_pointer(slot, original));
        if matches!(
            inferred,
            VariableType::Unknown(_) | VariableType::UnknownPointer
        ) {
            self.field_slot_types
                .get(&slot)
                .and_then(|evidence| evidence.candidate.clone())
                .unwrap_or(inferred)
        } else {
            inferred
        }
    }

    fn inferred_pointer(&self, slot: Slot, original: VariableType) -> VariableType {
        if original != VariableType::Unknown(Some(8)) {
            return original;
        }
        if let Some(id) = self.struct_ids.get(&slot) {
            return VariableType::Pointer(Box::new(VariableType::Struct(*id)));
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
            *ty = analysis.inferred_type(slot, ty.clone());
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
    analysis.propagate_fields();
    analysis.assign_struct_ids(program.structs.len());
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for (_, instr) in &function.body {
            analysis.pointee_instruction(instr, owner, program);
        }
    }
    analysis.propagate_pointees();
    // Pointee evidence can turn a loaded value into a typed pointer. Revisit
    // memory transfers so those pointer types become field types as well.
    for (index, function) in program.functions.iter().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for (_, instr) in &function.body {
            analysis.pointee_instruction(instr, owner, program);
        }
    }
    analysis.propagate_fields();
    analysis.propagate_field_types_to_slots();
    let definitions = analysis.struct_definitions(&program.structs);
    program.structs.extend(definitions);
    for (index, function) in program.functions.iter_mut().enumerate() {
        let owner = SyntheticFunctionId { id: index };
        for parameter in &mut function.parameters {
            match parameter {
                Parameter::Argument { ordinal, ty } => {
                    let slot = Slot::Argument(owner, *ordinal);
                    *ty = analysis.inferred_type(slot, ty.clone());
                }
                Parameter::Slot { variable, ty } => {
                    let slot = Slot::Variable(*variable);
                    *ty = analysis.inferred_type(slot, ty.clone());
                }
            }
        }
        for (_, instr) in &mut function.body {
            retype(instr, &analysis);
        }
    }
}
