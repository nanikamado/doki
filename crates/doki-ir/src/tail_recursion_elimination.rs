use crate::ast_step2::{
    Ast, BasicBlock, EndInstruction, Expr, Function, FxLambdaId, Instruction, VariableId,
};
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
                    f: f_id, tail_call, ..
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
                    fs.insert(*f_id);
                }
            }
        }
        tail_call_graph.insert(f.id, fs);
    }
    let mut recursions = FxHashMap::default();
    let mut inlining_order_rev = Vec::new();
    let mut done = FxHashSet::default();
    for f in &ast.functions {
        collect_recursion(
            f.id,
            &tail_call_graph,
            &mut recursions,
            &mut inlining_order_rev,
            &mut done,
            List::Nil,
        );
    }
    let mut functions: FxHashMap<_, _> = ast.functions.iter_mut().map(|f| (f.id, f)).collect();
    for id in inlining_order_rev.into_iter().rev() {
        let cycle = &recursions[&id];
        let f = functions.remove(&id).unwrap();
        let mut free_label = f.body.basic_blocks.len();
        let mut inlining_queue = VecDeque::new();
        let mut inlined_fns = FxHashMap::default();
        let current_function = InlinedFn {
            context: &f.context,
            parameter: f.parameter,
            label: 0,
        };
        inlined_fns.insert(id, current_function);
        for bb in &mut f.body.basic_blocks {
            eliminate_from_basic_block(
                bb,
                &functions,
                cycle,
                &mut free_label,
                &mut inlining_queue,
                &mut inlined_fns,
            );
        }
        while let Some((inlined_fn, label)) = inlining_queue.pop_front() {
            let blocks = functions[&inlined_fn].body.basic_blocks.iter().map(|bb| {
                let mut bb = add_offset_to_labels(bb, label);
                eliminate_from_basic_block(
                    &mut bb,
                    &functions,
                    cycle,
                    &mut free_label,
                    &mut inlining_queue,
                    &mut inlined_fns,
                );
                bb
            });
            f.body.basic_blocks.extend(blocks);
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct InlinedFn<'a> {
    context: &'a [crate::LocalVariable2],
    parameter: crate::LocalVariable2,
    label: usize,
}

fn eliminate_from_basic_block<'a>(
    bb: &mut BasicBlock,
    functions: &'a FxHashMap<FxLambdaId, &mut Function>,
    cycle: &FxHashSet<FxLambdaId>,
    free_label: &mut usize,
    inlining_queue: &mut VecDeque<(FxLambdaId, usize)>,
    inlined_fns: &mut FxHashMap<FxLambdaId, InlinedFn<'a>>,
) {
    match bb.instructions.last() {
        Some(Instruction::Assign(
            _,
            Expr::Call {
                f,
                tail_call,
                ctx,
                a,
            },
        )) if *tail_call.borrow() => {
            let ctx = *ctx;
            let a = *a;
            let f = *f;
            if let Some(&f) = inlined_fns.get(&f) {
                bb.instructions.pop();
                for (i, ctx_v) in f.context.iter().enumerate() {
                    bb.instructions.push(Instruction::Assign(
                        *ctx_v,
                        Expr::BasicCall {
                            args: vec![ctx],
                            id: crate::ast_step2::BasicFunction::FieldAccessor { field: i },
                        },
                    ))
                }
                bb.instructions
                    .push(Instruction::Assign(f.parameter, Expr::Ident(a)));
                bb.end_instruction = EndInstruction::Goto { label: f.label };
            } else if cycle.contains(&f) {
                bb.instructions.pop();
                let called_fn = &functions[&f];
                for (i, ctx_v) in called_fn.context.iter().enumerate() {
                    bb.instructions.push(Instruction::Assign(
                        *ctx_v,
                        Expr::BasicCall {
                            args: vec![ctx],
                            id: crate::ast_step2::BasicFunction::FieldAccessor { field: i },
                        },
                    ))
                }
                bb.instructions
                    .push(Instruction::Assign(called_fn.parameter, Expr::Ident(a)));
                bb.end_instruction = EndInstruction::Goto { label: *free_label };
                inlining_queue.push_back((f, *free_label));
                inlined_fns.insert(
                    f,
                    InlinedFn {
                        context: &called_fn.context,
                        parameter: called_fn.parameter,
                        label: *free_label,
                    },
                );
                *free_label += called_fn.body.basic_blocks.len();
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
                tester: *tester,
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
    inlining_order: &mut Vec<FxLambdaId>,
    done: &mut FxHashSet<FxLambdaId>,
    trace: List,
) {
    if done.contains(&f) {
    } else if let Some(v) = trace.take_until(f) {
        recursions.entry(f).or_default().extend(v.iter());
    } else {
        let trace = List::Cons(f, &trace);
        for f in &tail_call_graph[&f] {
            collect_recursion(*f, tail_call_graph, recursions, inlining_order, done, trace)
        }
        if recursions.contains_key(&f) {
            inlining_order.push(f);
        }
        done.insert(f);
    }
}
