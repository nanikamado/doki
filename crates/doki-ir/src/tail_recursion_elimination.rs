use crate::ast_step2::{
    Ast, BasicBlock, EndInstruction, Expr, Function, FxLambdaId, Instruction, VariableId,
};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;

pub fn run(ast: &mut Ast) {
    let mut tail_call_graph = FxHashMap::default();
    for f in &ast.functions {
        let mut fs = FxHashSet::default();
        for bb in &f.body.basic_blocks {
            let mut e = &bb.end_instruction;
            if let Some(Instruction::Assign(
                v,
                Expr::Call {
                    real_function,
                    tail_call,
                    ..
                },
            )) = bb.instructions.last()
            {
                let tc = loop {
                    match e {
                        EndInstruction::Ret(VariableId::Local(ret)) => break ret == v,
                        EndInstruction::Goto { label } => {
                            let bb = &f.body.basic_blocks[*label];
                            if bb.instructions.is_empty() {
                                e = &bb.end_instruction;
                            } else {
                                break false;
                            }
                        }
                        _ => break false,
                    }
                };
                if tc {
                    tail_call.replace(true);
                    fs.insert(*real_function);
                }
            }
        }
        tail_call_graph.insert(f.id, fs);
    }
    let mut recursions = FxHashMap::default();
    let mut done = FxHashSet::default();
    for f in &ast.functions {
        collect_recursion(
            f.id,
            &tail_call_graph,
            &mut recursions,
            &mut done,
            List::Nil,
        );
    }
    let recursions = sort_tail_recursive_fns(recursions);
    let mut functions: FxHashMap<_, _> = ast.functions.iter_mut().map(|f| (f.id, f)).collect();
    for (id, cycle) in &recursions {
        let f = functions.remove(id).unwrap();
        let original_block_len = f.body.basic_blocks.len();
        let mut added_block_len = 0;
        let mut inlining_queue = VecDeque::new();
        let current_function = FnProperty {
            id: *id,
            context: &f.context,
            parameter: f.parameter,
        };
        for bb in &mut f.body.basic_blocks {
            eliminate_from_basic_block(
                bb,
                &functions,
                current_function,
                cycle,
                original_block_len,
                &mut added_block_len,
                &mut inlining_queue,
            );
        }
        while let Some((offset, inlined_fn)) = inlining_queue.pop_front() {
            let blocks = functions[&inlined_fn].body.basic_blocks.iter().map(|bb| {
                let mut bb = add_offset_to_labels(bb, offset);
                eliminate_from_basic_block(
                    &mut bb,
                    &functions,
                    current_function,
                    cycle,
                    original_block_len,
                    &mut added_block_len,
                    &mut inlining_queue,
                );
                bb
            });
            f.body.basic_blocks.extend(blocks);
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct FnProperty<'a> {
    id: FxLambdaId,
    context: &'a [crate::LocalVariable2],
    parameter: crate::LocalVariable2,
}

fn eliminate_from_basic_block(
    bb: &mut BasicBlock,
    functions: &FxHashMap<FxLambdaId, &mut Function>,
    current_function: FnProperty,
    inlining_target: &FxHashSet<FxLambdaId>,
    original_block_len: usize,
    added_block_len: &mut usize,
    inlining_queue: &mut VecDeque<(usize, FxLambdaId)>,
) {
    match bb.instructions.last() {
        Some(Instruction::Assign(
            _,
            Expr::Call {
                real_function,
                tail_call,
                f: f_ctx,
                a,
            },
        )) if *tail_call.borrow() => {
            let f_ctx = *f_ctx;
            let a = *a;
            let real_function = *real_function;
            if real_function == current_function.id {
                bb.instructions.pop();
                for (i, ctx) in current_function.context.iter().enumerate() {
                    bb.instructions.push(Instruction::Assign(
                        *ctx,
                        Expr::BasicCall {
                            args: vec![f_ctx],
                            id: crate::ast_step2::BasicFunction::FieldAccessor { field: i },
                        },
                    ))
                }
                bb.instructions.push(Instruction::Assign(
                    current_function.parameter,
                    Expr::Ident(a),
                ));
                bb.end_instruction = EndInstruction::Goto { label: 0 };
            } else if inlining_target.contains(&real_function) {
                bb.instructions.pop();
                let called_fn = &functions[&real_function];
                for (i, ctx) in called_fn.context.iter().enumerate() {
                    bb.instructions.push(Instruction::Assign(
                        *ctx,
                        Expr::BasicCall {
                            args: vec![f_ctx],
                            id: crate::ast_step2::BasicFunction::FieldAccessor { field: i },
                        },
                    ))
                }
                bb.instructions
                    .push(Instruction::Assign(called_fn.parameter, Expr::Ident(a)));
                bb.end_instruction = EndInstruction::Goto {
                    label: original_block_len + *added_block_len,
                };
                *added_block_len += called_fn.body.basic_blocks.len();
                inlining_queue.push_back((*added_block_len, real_function));
            }
        }
        _ => (),
    }
}

fn add_offset_to_labels(b: &BasicBlock, offset: usize) -> BasicBlock {
    let end_instruction = match &b.end_instruction {
        EndInstruction::Goto { label } => EndInstruction::Goto {
            label: label + offset,
        },
        a => a.clone(),
    };
    let instructions = b
        .instructions
        .iter()
        .map(|i| match i {
            Instruction::Test {
                tester,
                operand,
                catch_label,
            } => Instruction::Test {
                tester: tester.clone(),
                operand: *operand,
                catch_label: catch_label + offset,
            },
            a => a.clone(),
        })
        .collect();
    BasicBlock {
        instructions,
        end_instruction,
    }
}

#[derive(Debug, Clone, Copy)]
enum List<'a> {
    Nil,
    Cons(FxLambdaId, &'a List<'a>),
}

impl List<'_> {
    fn take_until(self, id: FxLambdaId) -> Option<Vec<FxLambdaId>> {
        match self {
            List::Nil => None,
            List::Cons(h, t) => {
                if h == id {
                    Some(Vec::new())
                } else if let Some(mut v) = t.take_until(id) {
                    v.push(h);
                    Some(v)
                } else {
                    None
                }
            }
        }
    }
}

fn collect_recursion(
    f: FxLambdaId,
    tail_call_graph: &FxHashMap<FxLambdaId, FxHashSet<FxLambdaId>>,
    recursions: &mut FxHashMap<FxLambdaId, FxHashSet<FxLambdaId>>,
    done: &mut FxHashSet<FxLambdaId>,
    trace: List,
) {
    if done.contains(&f) {
    } else if let Some(v) = trace.take_until(f) {
        recursions.entry(f).or_default().extend(v.iter());
    } else {
        let trace = List::Cons(f, &trace);
        for f in &tail_call_graph[&f] {
            collect_recursion(*f, tail_call_graph, recursions, done, trace)
        }
        done.insert(f);
    }
}

fn sort_tail_recursive_fns(
    mut recursions: FxHashMap<FxLambdaId, FxHashSet<FxLambdaId>>,
) -> Vec<(FxLambdaId, FxHashSet<FxLambdaId>)> {
    let mut sorted = Vec::with_capacity(recursions.len());
    for f in recursions.keys().copied().collect_vec() {
        sort_tail_recursive_fns_aux(f, &mut sorted, &mut recursions);
    }
    sorted
}

fn sort_tail_recursive_fns_aux(
    f: FxLambdaId,
    sorted: &mut Vec<(FxLambdaId, FxHashSet<FxLambdaId>)>,
    recursions: &mut FxHashMap<FxLambdaId, FxHashSet<FxLambdaId>>,
) {
    if let Some(c) = recursions.remove(&f) {
        for f in &c {
            sort_tail_recursive_fns_aux(*f, sorted, recursions);
        }
        sorted.push((f, c));
    }
}
