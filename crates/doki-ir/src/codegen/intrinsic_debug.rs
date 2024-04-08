use super::Env;
use crate::ast_step1::TypePointer;
use crate::ast_step2::{CType, PrinterCollector};
use crate::codegen::Dis;
use crate::intrinsics::IntrinsicTypeTag;
use crate::TypeId;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::fmt::Display;

fn print_tag_args(
    f: &mut std::fmt::Formatter<'_>,
    tag: TypeId,
    arg: impl Display,
    fields: &[TypePointer],
    env: Env,
) -> std::fmt::Result {
    match tag {
        TypeId::Intrinsic(IntrinsicTypeTag::I64) => {
            write!(f, r#"fprintf(stderr, "%ld", {arg});"#)
        }
        TypeId::Intrinsic(IntrinsicTypeTag::U8) => {
            write!(f, r#"fprintf(stderr, "%d", {arg});"#)
        }
        TypeId::Intrinsic(IntrinsicTypeTag::F64) => {
            write!(f, r#"fprintf(stderr, "%g", {arg});"#)
        }
        TypeId::Intrinsic(IntrinsicTypeTag::Ptr) => {
            write!(f, r#"fprintf(stderr, "%p", {arg});"#)
        }
        _ => {
            write!(f, r#"fprintf(stderr, ""#)?;
            env.constructor_names.print_type_id(tag, f)?;
            if !fields.is_empty() {
                write!(f, r#"(");"#)?;
                write!(
                    f,
                    "{}",
                    fields
                        .iter()
                        .enumerate()
                        .format_with(r#"fprintf(stderr, ", ");"#, |(i, a), f| {
                            f(&format_args!("intrinsic_debug_{a}({arg}._{i});"))
                        })
                )?;
                write!(f, r#"fprintf(stderr, ")");"#)
            } else {
                write!(f, "\");")
            }
        }
    }
}

pub fn print_debug_printers(
    f: &mut std::fmt::Formatter<'_>,
    printer_collector: &PrinterCollector,
    printer_c_type: &FxHashMap<TypePointer, CType>,
    env: Env<'_>,
) -> std::fmt::Result {
    for p in printer_collector.inner().keys() {
        let c_t = printer_c_type[p];
        write!(
            f,
            "static struct t0 intrinsic_debug_{p}({} _0);",
            Dis(&c_t, env)
        )?;
    }
    for (p, ts) in printer_collector.inner() {
        let c_t = printer_c_type[p];
        write!(
            f,
            "static struct t0 intrinsic_debug_{p}({} _0){{",
            Dis(&c_t, env)
        )?;
        match ts.union_members.len() {
            0 => {
                write!(f, r#"panic("unexpected");"#)?;
            }
            1 => {
                let (tag, (fields, boxed)) = &ts.union_members[0];
                if *boxed {
                    print_tag_args(f, *tag, "(*_0)", fields, env)?;
                } else {
                    print_tag_args(f, *tag, "_0", fields, env)?;
                }
            }
            _ => {
                write!(f, "switch(_0.tag){{")?;
                for (i, (tag, (fields, boxed))) in ts.union_members[1..].iter().enumerate() {
                    let boxed = if *boxed { "*" } else { "" };
                    write!(f, "case {}:", i + 1)?;
                    print_tag_args(
                        f,
                        *tag,
                        format_args!("({boxed}_0.value._{})", i + 1),
                        fields,
                        env,
                    )?;
                    write!(f, "break;")?;
                }
                write!(f, "default:")?;
                let (tag, (fields, boxed)) = &ts.union_members[0];
                let boxed = if *boxed { "*" } else { "" };
                print_tag_args(f, *tag, format_args!("({boxed}_0.value._0)"), fields, env)?;
                write!(f, "}}")?;
            }
        }
        write!(f, "return (struct t0){{}};}}")?;
    }
    Ok(())
}
