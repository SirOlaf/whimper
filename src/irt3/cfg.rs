//! Recover the complete control-flow graph, including structured loop edges.

use std::collections::{HashMap, HashSet};

use super::ir::{IRExpr, IRInst, LoopId, Program};

pub(super) type NodeId = usize;

#[derive(Clone)]
pub(super) enum Transfer {
    Goto(NodeId),
    Branch {
        condition: IRExpr,
        then_node: NodeId,
        else_node: NodeId,
    },
    Exit(IRInst),
}

#[derive(Clone)]
pub(super) struct Node {
    pub offset: usize,
    pub body: Vec<(usize, IRInst)>,
    pub transfer: Transfer,
}

impl Node {
    pub fn successors(&self) -> Vec<NodeId> {
        match self.transfer {
            Transfer::Goto(target) => vec![target],
            Transfer::Branch {
                then_node,
                else_node,
                ..
            } if then_node != else_node => {
                vec![then_node, else_node]
            }
            Transfer::Branch { then_node, .. } => vec![then_node],
            Transfer::Exit(_) => Vec::new(),
        }
    }
}

pub(super) struct Cfg {
    pub entry: NodeId,
    pub nodes: Vec<Node>,
}

#[derive(Clone, Default)]
struct LoopTargets {
    enclosing: Option<(NodeId, NodeId)>,
    labeled: HashMap<LoopId, NodeId>,
}

impl Cfg {
    fn node(&mut self, offset: usize, body: Vec<(usize, IRInst)>, transfer: Transfer) -> NodeId {
        let id = self.nodes.len();
        self.nodes.push(Node {
            offset,
            body,
            transfer,
        });
        id
    }

    fn sequence(
        &mut self,
        body: Vec<(usize, IRInst)>,
        mut next: NodeId,
        loops: &LoopTargets,
    ) -> NodeId {
        for (offset, instr) in body.into_iter().rev() {
            next = match instr {
                IRInst::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    let then_node = self.sequence(
                        then_branch
                            .into_iter()
                            .map(|instr| (offset, instr))
                            .collect(),
                        next,
                        loops,
                    );
                    let else_node = self.sequence(
                        else_branch
                            .into_iter()
                            .map(|instr| (offset, instr))
                            .collect(),
                        next,
                        loops,
                    );
                    self.node(
                        offset,
                        Vec::new(),
                        Transfer::Branch {
                            condition,
                            then_node,
                            else_node,
                        },
                    )
                }
                IRInst::Loop {
                    label,
                    entry_offset,
                    body,
                } => {
                    let header = self.node(entry_offset, Vec::new(), Transfer::Goto(next));
                    let mut nested = loops.clone();
                    nested.enclosing = Some((next, header));
                    if let Some(label) = label {
                        nested.labeled.insert(label, header);
                    }
                    // Falling through a loop body repeats it as well.
                    let start = self.sequence(body, header, &nested);
                    self.nodes[header].transfer = Transfer::Goto(start);
                    header
                }
                IRInst::Break => loops.enclosing.expect("break outside a T3 loop").0,
                IRInst::Continue => loops.enclosing.expect("continue outside a T3 loop").1,
                IRInst::ContinueLoop(label) => loops.labeled[&label],
                // Function entry nodes occupy the first program.functions.len() slots.
                // Argument assignments have already been materialized by the inliner.
                IRInst::CallSynthetic {
                    function,
                    arguments,
                } => {
                    assert!(arguments.is_empty());
                    function.id
                }
                instr @ (IRInst::Return(_) | IRInst::Jump(_) | IRInst::End) => {
                    self.node(offset, Vec::new(), Transfer::Exit(instr))
                }
                instr => self.node(offset, vec![(offset, instr)], Transfer::Goto(next)),
            };
        }
        next
    }

    pub fn build(program: Program) -> Self {
        let mut cfg = Self {
            entry: program.entry.unwrap().id,
            nodes: Vec::new(),
        };
        for function in &program.functions {
            cfg.node(
                function.entry_offset,
                Vec::new(),
                Transfer::Exit(IRInst::End),
            );
        }
        for (id, function) in program.functions.into_iter().enumerate() {
            let end = cfg.node(
                function.entry_offset,
                Vec::new(),
                Transfer::Exit(IRInst::End),
            );
            let start = cfg.sequence(function.body, end, &LoopTargets::default());
            cfg.nodes[id].transfer = Transfer::Goto(start);
        }
        cfg
    }

    pub fn reachable(&self) -> HashSet<NodeId> {
        let mut found = HashSet::new();
        let mut pending = vec![self.entry];
        while let Some(node) = pending.pop() {
            if found.insert(node) {
                pending.extend(self.nodes[node].successors());
            }
        }
        found
    }

    fn predecessors(&self, reachable: &HashSet<NodeId>) -> Vec<Vec<NodeId>> {
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for &node in reachable {
            for successor in self.nodes[node].successors() {
                predecessors[successor].push(node);
            }
        }
        predecessors
    }

    /// Iteratively absorb blocks which have exactly one incoming CFG edge.
    /// Shared continuations stay separate until the branch structuring step.
    pub fn eliminate_branches(&mut self) {
        loop {
            let reachable = self.reachable();
            let predecessors = self.predecessors(&reachable);
            let mut changed = false;
            for id in 0..self.nodes.len() {
                if !reachable.contains(&id) {
                    continue;
                }
                if let Transfer::Branch {
                    condition: IRExpr::Bool(value),
                    then_node,
                    else_node,
                } = self.nodes[id].transfer
                {
                    self.nodes[id].transfer =
                        Transfer::Goto(if value { then_node } else { else_node });
                    changed = true;
                    break;
                }
                let Transfer::Goto(target) = self.nodes[id].transfer else {
                    continue;
                };
                if target == id || target == self.entry || predecessors[target].len() != 1 {
                    continue;
                }
                let successor = self.nodes[target].clone();
                self.nodes[id].body.extend(successor.body);
                self.nodes[id].offset = successor.offset;
                self.nodes[id].transfer = successor.transfer;
                changed = true;
                break;
            }
            if !changed {
                break;
            }
        }
        // Analyses below only need the remaining reachable blocks, not the
        // individual instructions which were absorbed while eliminating edges.
        let reachable = self.reachable();
        let mut ids = vec![0; self.nodes.len()];
        let mut next = 0;
        for (id, mapped) in ids.iter_mut().enumerate() {
            if reachable.contains(&id) {
                *mapped = next;
                next += 1;
            }
        }
        self.nodes = std::mem::take(&mut self.nodes)
            .into_iter()
            .enumerate()
            .filter_map(|(id, mut node)| {
                if !reachable.contains(&id) {
                    return None;
                }
                match &mut node.transfer {
                    Transfer::Goto(target) => *target = ids[*target],
                    Transfer::Branch {
                        then_node,
                        else_node,
                        ..
                    } => {
                        *then_node = ids[*then_node];
                        *else_node = ids[*else_node];
                    }
                    Transfer::Exit(_) => {}
                }
                Some(node)
            })
            .collect();
        self.entry = ids[self.entry];
    }

    /// A common postdominator is the continuation shared by both branch arms.
    /// A virtual exit joins returns, external jumps and End. Closed cycles have
    /// no exit and must not invent a continuation outside their infinite loop.
    pub fn postdominators(&self) -> Vec<Option<NodeId>> {
        let reachable = self.reachable();
        let predecessors = self.predecessors(&reachable);
        let exit = self.nodes.len();
        let mut exiting = HashSet::from([exit]);
        let mut pending: Vec<_> = reachable
            .iter()
            .copied()
            .filter(|&id| matches!(self.nodes[id].transfer, Transfer::Exit(_)))
            .collect();
        while let Some(id) = pending.pop() {
            if exiting.insert(id) {
                pending.extend(predecessors[id].iter().copied());
            }
        }
        let mut sets: Vec<_> = (0..=exit)
            .map(|id| {
                if id != exit && exiting.contains(&id) {
                    exiting.clone()
                } else {
                    HashSet::from([id])
                }
            })
            .collect();
        loop {
            let mut changed = false;
            for id in 0..exit {
                if !exiting.contains(&id) {
                    continue;
                }
                let mut successors = self.nodes[id].successors();
                if successors.is_empty() {
                    successors.push(exit);
                }
                let mut set = sets[successors[0]].clone();
                for &successor in &successors[1..] {
                    set.retain(|node| sets[successor].contains(node));
                }
                set.insert(id);
                if set != sets[id] {
                    sets[id] = set;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        (0..exit)
            .map(|id| {
                (0..exit).find(|&candidate| {
                    candidate != id
                        && sets[id].contains(&candidate)
                        && sets[id].iter().all(|&other| {
                            other == id || other == candidate || !sets[other].contains(&candidate)
                        })
                })
            })
            .collect()
    }
}
