//! Post-translation assumptions report.
//!
//! After merge, a `FnDecl` that never met a definition is emitted as an
//! *assumed* Pulse `fn` (its contract is trusted, its body is
//! `unreachable`), and a `StructDecl` without a definition becomes an
//! abstract `assume val` type. Verification silently rests on these
//! assumptions; this pass collects them so the user gets an explicit list
//! of the definitions and specifications they still have to provide.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ir::*;

pub struct AssumedFn {
    pub name: Rc<str>,
    pub loc: Location,
    pub has_spec: bool,
    pub is_pure: bool,
    pub call_sites: usize,
}

pub struct OpaqueType {
    pub name: Rc<str>,
    pub loc: Location,
}

pub struct AssumptionsReport {
    pub assumed_fns: Vec<AssumedFn>,
    pub opaque_types: Vec<OpaqueType>,
}

/// Count function-name occurrences in call position, in function bodies and
/// in contract expressions. (Calls inside type refinements are not counted;
/// a refinement mentioning an assumed pure fn still shows up via its decl.)
struct CallCounter {
    counts: HashMap<Rc<str>, usize>,
}

impl CallCounter {
    fn expr(&mut self, rv: &Expr) {
        match &rv.val {
            ExprT::FnCall(f, args) => {
                *self.counts.entry(f.val.clone()).or_default() += 1;
                for arg in args {
                    self.expr(arg);
                }
            }
            // A bare function reference (`&f` / function-to-pointer decay) is
            // not a call; the counter tracks call position only.
            ExprT::FnRef(_)
            | ExprT::Var(_)
            | ExprT::BoolLit(_)
            | ExprT::IntLit(..)
            | ExprT::FloatLit(..) => {}
            ExprT::FnPtrCall(callee, args) => {
                self.expr(callee);
                for arg in args {
                    self.expr(arg);
                }
            }
            ExprT::Deref(x)
            | ExprT::Member(x, _)
            | ExprT::VAttr(_, x)
            | ExprT::Ref(x)
            | ExprT::Cast(x, _)
            | ExprT::Free(x)
            | ExprT::ContainerOf(x, _, _)
            | ExprT::PreIncr(x)
            | ExprT::PostIncr(x)
            | ExprT::PreDecr(x)
            | ExprT::PostDecr(x)
            | ExprT::UnOp(_, x)
            | ExprT::Live(x)
            | ExprT::Old(x)
            | ExprT::MallocArray(_, x)
            | ExprT::CallocArray(_, x)
            | ExprT::MallocFlex(_, x)
            | ExprT::CallocFlex(_, x)
            | ExprT::MemsetZero(_, x)
            | ExprT::Forall(_, _, x)
            | ExprT::Exists(_, _, x)
            | ExprT::UnionInit(_, _, x) => self.expr(x),
            ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprT::Memset(_, a, b, c) => {
                self.expr(a);
                self.expr(b);
                self.expr(c);
            }
            ExprT::Cond(a, b, c) => {
                self.expr(a);
                self.expr(b);
                self.expr(c);
            }
            ExprT::StructInit(_, fields) => {
                for (_, v) in fields {
                    self.expr(v);
                }
            }
            ExprT::ArrayInit { elems, .. } => {
                for e in elems {
                    self.expr(e);
                }
            }
            ExprT::InlinePulse(code, _) => self.inline_pulse(code),
            ExprT::Error(_)
            | ExprT::SizeOf(_)
            | ExprT::AlignOf(_)
            | ExprT::Malloc(_)
            | ExprT::Calloc(_) => {}
        }
    }

    fn inline_pulse(&mut self, code: &InlinePulseCode) {
        for tok in &code.tokens {
            match tok {
                InlinePulseToken::RValueAntiquot { expr, .. }
                | InlinePulseToken::LValueAntiquot { expr, .. } => self.expr(expr),
                InlinePulseToken::TypeAntiquot { .. }
                | InlinePulseToken::Declare { .. }
                | InlinePulseToken::Verbatim(_)
                | InlinePulseToken::FieldAntiquot { .. }
                | InlinePulseToken::AuxFnAntiquot { .. } => {}
            }
        }
    }

    fn exprs(&mut self, rvs: &Exprs) {
        for rv in rvs {
            self.expr(rv);
        }
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match &stmt.val {
            StmtT::Call(x) | StmtT::Assert(x) | StmtT::Let(_, _, x) => self.expr(x),
            StmtT::Decl(_, _) => {}
            StmtT::DeclStackArray { size, .. } => self.expr(size),
            StmtT::Assign(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            StmtT::If {
                cond,
                then_branch,
                else_branch,
                ensures,
            } => {
                self.expr(cond);
                self.exprs(ensures);
                self.stmts(then_branch);
                self.stmts(else_branch);
            }
            StmtT::Match {
                scrutinee,
                branches,
                default_branch,
                ensures,
            } => {
                self.expr(scrutinee);
                self.exprs(ensures);
                for branch in branches.iter() {
                    self.exprs(&branch.patterns);
                    self.stmts(&branch.body);
                }
                self.stmts(default_branch);
            }
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => {
                self.expr(cond);
                self.exprs(inv);
                self.exprs(requires);
                self.exprs(ensures);
                self.stmts(body);
            }
            StmtT::Return(x) => {
                if let Some(x) = x {
                    self.expr(x)
                }
            }
            StmtT::GhostStmt(code) => self.inline_pulse(code),
            StmtT::Label { ensures, .. } => self.exprs(ensures),
            StmtT::GotoBlock { body, ensures, .. } => {
                self.stmts(body);
                self.exprs(ensures);
            }
            StmtT::Break | StmtT::Continue | StmtT::Goto(_) | StmtT::Error => {}
        }
    }

    fn stmts(&mut self, stmts: &Vec<Rc<Stmt>>) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }
}

pub fn collect(tu: &TranslationUnit) -> AssumptionsReport {
    let mut counter = CallCounter {
        counts: HashMap::new(),
    };
    for decl in &tu.decls {
        match &decl.val {
            DeclT::FnDefn(FnDefn { decl, body }) => {
                counter.exprs(&decl.requires);
                counter.exprs(&decl.ensures);
                counter.stmts(body);
            }
            DeclT::FnDecl(fn_decl) => {
                counter.exprs(&fn_decl.requires);
                counter.exprs(&fn_decl.ensures);
            }
            _ => {}
        }
    }

    let mut assumed_fns = vec![];
    let mut opaque_types = vec![];
    for decl in &tu.decls {
        match &decl.val {
            DeclT::FnDecl(fn_decl) => {
                let name = fn_decl.name.val.clone();
                // Internal anchors generated by pal.h macros are not user
                // assumptions.
                if name.starts_with("__pal") {
                    continue;
                }
                assumed_fns.push(AssumedFn {
                    call_sites: counter.counts.get(&name).copied().unwrap_or(0),
                    name,
                    loc: fn_decl.name.loc.location().clone(),
                    has_spec: !fn_decl.requires.is_empty() || !fn_decl.ensures.is_empty(),
                    is_pure: fn_decl.is_pure,
                });
            }
            DeclT::StructDecl(name) => {
                opaque_types.push(OpaqueType {
                    name: name.val.clone(),
                    loc: name.loc.location().clone(),
                });
            }
            _ => {}
        }
    }

    // Spec-less functions first (they need action), then by call count.
    assumed_fns.sort_by(|a, b| {
        (a.has_spec, std::cmp::Reverse(a.call_sites), a.name.clone()).cmp(&(
            b.has_spec,
            std::cmp::Reverse(b.call_sites),
            b.name.clone(),
        ))
    });

    AssumptionsReport {
        assumed_fns,
        opaque_types,
    }
}

fn fmt_loc(loc: &Location) -> String {
    let file = std::env::current_dir()
        .ok()
        .and_then(|cwd| {
            std::path::Path::new(&*loc.file_name)
                .strip_prefix(&cwd)
                .ok()
                .map(|p| p.to_string_lossy().into_owned())
        })
        .unwrap_or_else(|| loc.file_name.to_string());
    format!("{}:{}", file, loc.range.start.line)
}

impl AssumptionsReport {
    pub fn is_empty(&self) -> bool {
        self.assumed_fns.is_empty() && self.opaque_types.is_empty()
    }

    /// Compact summary printed to stderr after translation.
    pub fn to_stderr_summary(&self) -> String {
        let mut out = String::new();
        let no_spec: Vec<_> = self.assumed_fns.iter().filter(|f| !f.has_spec).collect();
        let with_spec = self.assumed_fns.len() - no_spec.len();
        out += &format!(
            "note: {} function(s) have no body and are assumed",
            self.assumed_fns.len()
        );
        if with_spec > 0 {
            out += &format!(" ({} with a user spec, trusted as axioms)", with_spec);
        }
        out += "\n";
        if !no_spec.is_empty() {
            out += &format!(
                "note: {} of them have NO specification — callers learn nothing about \
                 their result beyond default ownership:\n",
                no_spec.len()
            );
            for f in &no_spec {
                out += &format!(
                    "        {} ({}, {} call site{})\n",
                    f.name,
                    fmt_loc(&f.loc),
                    f.call_sites,
                    if f.call_sites == 1 { "" } else { "s" }
                );
            }
        }
        if !self.opaque_types.is_empty() {
            out += &format!(
                "note: {} opaque type(s) with unknown layout (ownership predicate assumed):\n",
                self.opaque_types.len()
            );
            for t in &self.opaque_types {
                out += &format!("        struct {} ({})\n", t.name, fmt_loc(&t.loc));
            }
        }
        out
    }

    /// Detailed markdown written next to the generated modules.
    pub fn to_markdown(&self) -> String {
        let mut out = String::from(
            "# Translation assumptions\n\n\
             Declarations without a definition are emitted as *assumed* Pulse \
             modules: their contract is taken on faith and their body is never \
             checked. This file lists everything the verification will silently \
             trust, so each entry is a pointer to work that remains.\n",
        );

        let no_spec: Vec<_> = self.assumed_fns.iter().filter(|f| !f.has_spec).collect();
        let with_spec: Vec<_> = self.assumed_fns.iter().filter(|f| f.has_spec).collect();

        if !no_spec.is_empty() {
            out += &format!(
                "\n## Functions assumed with NO specification ({})\n\n\
                 Only the default ownership contract is emitted; results are \
                 otherwise unconstrained. Add `_requires`/`_ensures` to the \
                 declaration (or provide a definition) to make calls meaningful.\n\n\
                 | function | declared at | call sites | pure |\n\
                 |---|---|---|---|\n",
                no_spec.len()
            );
            for f in no_spec {
                out += &format!(
                    "| `{}` | {} | {} | {} |\n",
                    f.name,
                    fmt_loc(&f.loc),
                    f.call_sites,
                    if f.is_pure { "yes" } else { "" }
                );
            }
        }

        if !with_spec.is_empty() {
            out += &format!(
                "\n## Functions assumed with a user specification ({})\n\n\
                 Trusted as axioms — the spec is used by callers but never \
                 checked against an implementation.\n\n\
                 | function | declared at | call sites | pure |\n\
                 |---|---|---|---|\n",
                with_spec.len()
            );
            for f in with_spec {
                out += &format!(
                    "| `{}` | {} | {} | {} |\n",
                    f.name,
                    fmt_loc(&f.loc),
                    f.call_sites,
                    if f.is_pure { "yes" } else { "" }
                );
            }
        }

        if !self.opaque_types.is_empty() {
            out += &format!(
                "\n## Opaque types ({})\n\n\
                 Forward-declared but never defined: the layout is unknown and \
                 the ownership predicate is an abstract `assume val`. Field \
                 accesses on these types cannot be translated.\n\n\
                 | type | declared at |\n\
                 |---|---|\n",
                self.opaque_types.len()
            );
            for t in &self.opaque_types {
                out += &format!("| `struct {}` | {} |\n", t.name, fmt_loc(&t.loc));
            }
        }

        out
    }
}
