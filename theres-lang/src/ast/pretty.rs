use crate::ast::{
    AstId, Bind, BindItem, BindItemKind, Block, Expr, ExprType, Field, FnDecl, Instance, Name,
    Path, Realm, Stmt, StmtKind, Thing, ThingKind, Ty, TyKind, Universe, VariableStmt, Visitor,
};

use crate::id::IndexId;
use crate::lexer::Span;
use crate::symbols::SymbolId;
use crate::visitor_common::VisitorResult;

use std::fmt::{self, Write as _};
use std::io::{self, Write};

pub struct PrettyPrinter<'ast, O> {
    writer: &'ast mut O,
    indent: usize,

    indent_jump: usize,
}

impl<'ast, O> PrettyPrinter<'ast, O> {
    pub fn new(writer: &'ast mut O) -> Self {
        Self::new_with_indent(2, writer)
    }

    pub fn new_with_indent(indent_jump: usize, writer: &'ast mut O) -> Self {
        Self {
            writer,
            indent: 0,
            indent_jump,
        }
    }
}

impl<O> fmt::Write for PrettyPrinter<'_, O>
where
    O: Write,
{
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for _ in 0..self.indent {
            self.write_arbitrary(" ");
        }

        self.write_arbitrary(s);

        Ok(())
    }
}

impl<O> PrettyPrinter<'_, O>
where
    O: Write,
{
    // pub fn write_indent(&mut self) {
    //     for _ in 0..self.indent {
    //         self.write_arbitrary(" ");
    //     }
    // }

    pub fn write_span(&mut self, span: Span) {
        if span == Span::DUMMY {
            return self.write_arbitrary("synthetic");
        }

        let _ = write!(self.writer, "{}@{}/{}", span.line, span.start, span.end);
    }

    pub fn write_location_id<A: IndexId>(&mut self, span: Span, id: A) {
        self.write_arbitrary("  <");
        self.write_arbitrary(A::own_name());
        self.write_arbitrary("#");
        let _ = write!(self.writer, "{} -- ", id.idx());
        self.write_span(span);
        let _ = writeln!(self.writer, ">");
    }

    pub fn write(
        &mut self,
        what: &str,
        span: Span,
        id: AstId,
        name: Option<Name>,
        extra: Option<&str>,
    ) {
        self.write_fallible(what, span, id, name, extra)
            .expect("`write_fallible` failed!");
    }

    pub fn write_fallible(
        &mut self,
        what: &str,
        span: Span,
        id: AstId,
        name: Option<Name>,
        extra: Option<&str>,
    ) -> io::Result<()> {
        // horrible
        for _ in 0..self.indent {
            write!(self.writer, " ")?;
        }

        write!(self.writer, "{what}")?;

        if let Some(extra) = extra {
            write!(self.writer, " ({extra})")?;
        }

        if let Some(name) = name {
            write!(
                self.writer,
                "(name: {})",
                SymbolId::get_interned(&name.interned)
            )?;
        }

        self.write_location_id(span, id);

        Ok(())
    }

    pub fn write_arbitrary(&mut self, s: &str) {
        write!(self.writer, "{s}").expect("writer failed");
    }

    pub fn increase_indent<F, R>(&mut self, work: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let old = self.indent;
        self.indent += self.indent_jump;
        let ret = work(self);
        self.indent = old;
        ret
    }

    pub fn travel(&mut self, universe: &Universe) {
        self.write("Universe", universe.span, universe.id, None, None);

        self.increase_indent(|me| {
            for i in &universe.thingies {
                me.visit_thing(i);
                me.writer.write_all(b"\n").expect("writer failed");
            }
        });
    }
}

impl<'ast, 'v, O> Visitor<'v> for PrettyPrinter<'ast, O>
where
    O: Write,
    'ast: 'v,
{
    type Result = ();

    fn visit_realm(&mut self, val: &'v Realm) -> Self::Result {
        self.write("Realm", val.span, AstId::DUMMY, Some(val.name), None);

        self.increase_indent(|this| {
            for t in &val.items {
                this.visit_thing(t);
            }
        });
    }

    fn visit_thing(&mut self, val: &'v Thing) -> Self::Result {
        match &val.kind {
            ThingKind::Function(f) => self.visit_fn_decl(f),
            ThingKind::Instance(i) => self.visit_instance(i),
            ThingKind::Bind(a) => self.visit_bind(a),
            ThingKind::Realm(r) => self.visit_realm(r),
        }
    }

    fn visit_fn_decl(&mut self, val: &'v FnDecl) -> Self::Result {
        self.write("Function", val.span, val.id, Some(val.sig.name), None);

        self.increase_indent(|t| t.visit_block(&val.block));

        let _ = writeln!(self);
    }

    fn visit_bind(&mut self, val: &'v Bind) -> Self::Result {
        self.write("Bind", val.span, val.id, None, None);

        self.increase_indent(|this| {
            for item in &val.items {
                this.visit_bind_item(item);
            }
        });
    }

    fn visit_bind_item(&mut self, val: &'v BindItem) -> Self::Result {
        match val.kind {
            BindItemKind::Const(ref constant) => self.visit_var_stmt(constant),
            BindItemKind::Fun(ref f) => self.visit_fn_decl(f),
        }
    }

    fn visit_instance(&mut self, val: &'v Instance) -> Self::Result {
        self.write("Instance", val.span, val.id, Some(val.name), None);

        self.increase_indent(|t| {
            for field in &val.fields {
                t.visit_field(field);
            }
        });
    }

    fn visit_block(&mut self, val: &'v Block) -> Self::Result {
        self.write("Block", val.span, val.id, None, None);

        self.increase_indent(|t| {
            for stmt in &val.stmts {
                t.visit_stmt(stmt);
            }
        });
    }

    fn visit_stmt(&mut self, val: &'v Stmt) -> Self::Result {
        match &val.kind {
            StmtKind::Expr(e) => {
                self.write("ExprStmt", val.span, val.id, None, None);
                self.increase_indent(|this| this.visit_expr(e));
            }

            StmtKind::LocalVar(local) => self.visit_var_stmt(local),

            StmtKind::Thing(thing) => {
                self.increase_indent(|t| t.visit_thing(thing));
            }
        }
    }

    fn visit_expr(&mut self, val: &'v Expr) -> Self::Result {
        self.write("Expr", val.span, val.id, None, None);

        self.increase_indent(|this| match &val.ty {
            ExprType::Path(path) => this.visit_path(path),

            ExprType::FunCall { callee, args } => {
                let _ = writeln!(this, "FunCall");

                this.increase_indent(|this| {
                    let _ = writeln!(this, "Callee");

                    this.indent += 1;
                    this.visit_expr(callee);
                    this.indent -= 1;

                    let _ = writeln!(this, "Arguments");
                    if args.is_empty() {
                        let _ = writeln!(this, "  empty!");
                    } else {
                        let _ = writeln!(this, "(");
                        this.indent += 3;
                        for e in args {
                            this.visit_expr(e);
                        }
                        this.indent -= 3;
                        let _ = writeln!(this, ")");
                    }
                });
            }

            _ => (),
        });
    }

    fn visit_path(&mut self, val: &'v Path) -> Self::Result {
        let string = path_to_string(val);
        self.write("Path", val.span, val.id, None, Some(&string));
    }

    fn visit_var_stmt(&mut self, val: &'v VariableStmt) -> Self::Result {
        self.write("Binding", val.name.span, val.id, Some(val.name), None);
        self.increase_indent(|this| {
            crate::maybe_visit!(v:this, m: visit_ty, &val.ty);

            if let Some(init) = &val.init {
                this.visit_expr(init);
            }
        });

        let _ = writeln!(self);
    }

    fn visit_field(&mut self, val: &'v Field) -> Self::Result {
        let c = if val.constant { "constant" } else { "mutable" };
        self.write("Field", val.span, val.id, Some(val.name), Some(c));

        self.increase_indent(|t| t.visit_ty(&val.ty));
    }

    fn visit_ty(&mut self, val: &'v Ty) -> Self::Result {
        let desc = ty_kind_to_string(&val.kind);
        self.write("Type", val.span, val.id, None, Some(&desc));
    }
}

// fn thing_kind_to_name(kind: &ThingKind) -> &'static str {
//     match kind {
//         ThingKind::Function(..) => "Function",
//         ThingKind::Global(..) => "Global",
//         ThingKind::Instance(..) => "Instance",
//         ThingKind::Bind(..) => "Bind",
//         ThingKind::Interface(..) => "Interface",
//         ThingKind::Realm(..) => "Realm",
//     }
// }

fn ty_kind_to_string(kind: &TyKind) -> String {
    let mut buf = String::new();

    match kind {
        TyKind::Path(path) => path_to_string(path),
        TyKind::MethodSelf => "Self".to_string(),
        TyKind::Fn { args, ret } => {
            buf.push_str("fun(");
            let strings = args.iter().map(|x| ty_kind_to_string(&x.kind));

            for s in strings {
                buf.push_str(&s);
            }

            buf.push(')');

            let ret_ty = ret
                .as_ref()
                .map_or("Nil".to_string(), |ty| ty_kind_to_string(&ty.kind));

            buf.push_str(&ret_ty);

            buf
        }

        TyKind::Array(ty) => ty_kind_to_string(&ty.kind),

        TyKind::Err => "{type err}".to_string(),
        TyKind::Infer => "{infer}".to_string(),
    }
}

fn path_to_string(path: &Path) -> String {
    let mut buf = String::new();

    for seg in &path.path {
        buf.push_str("::");
        buf.push_str(SymbolId::get_interned(&seg.name.interned));
    }

    buf
}
