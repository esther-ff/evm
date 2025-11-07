use crate::{
    pill::{
        access::{Access, AccessKind},
        body::Pill,
        cfg::{BasicBlock, BbData, BlockExit, Operand, Rvalue, Stmt, StmtKind},
    },
    session::Session,
};

pub trait PillVisitor<'vis> {
    fn cx(&self) -> &'vis Session<'vis>;

    fn visit_body(&mut self, body: &'vis mut Pill<'vis>) {
        for (bb, data) in body.cfg.blocks_mut() {
            self.visit_basic_block(bb, data);
        }
    }

    fn visit_basic_block(&mut self, _bb: BasicBlock, data: &mut BbData<'vis>) {
        for ele in data.stmts_mut() {
            self.visit_stmt(ele);
        }

        self.visit_block_exit(data.exit_mut());
    }

    fn visit_block_exit(&mut self, _exit: &mut BlockExit<'vis>) {}

    fn visit_stmt(&mut self, stmt: &mut Stmt<'vis>) {
        visit_stmt(self, stmt);
    }

    fn visit_operand(&mut self, op: &mut Operand<'vis>) {
        visit_operand(self, op);
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'vis>) {
        visit_rvalue(self, rvalue);
    }

    fn visit_access(&mut self, access: &mut Access<'vis>) {
        visit_access(self, access);
    }
}

pub fn visit_rvalue<'vis, V>(vis: &mut V, rvalue: &mut Rvalue<'vis>)
where
    V: PillVisitor<'vis> + ?Sized,
{
    match rvalue {
        Rvalue::Binary { lhs, rhs, .. } => {
            vis.visit_operand(lhs);
            vis.visit_operand(rhs);
        }

        Rvalue::Unary { val, .. } | Rvalue::Regular(val) => vis.visit_operand(val),

        Rvalue::List(vals) => {
            for ele in vals {
                vis.visit_operand(ele);
            }
        }

        Rvalue::Adt { args, .. } => {
            for ele in args {
                vis.visit_operand(ele);
            }
        }

        Rvalue::Length(acc) | Rvalue::AddrOf(acc) => vis.visit_access(acc),
    }
}

pub fn visit_stmt<'vis, V>(vis: &mut V, stmt: &mut Stmt<'vis>)
where
    V: PillVisitor<'vis> + ?Sized,
{
    match stmt.kind_mut() {
        StmtKind::Assign { dest, src, .. } => {
            vis.visit_access(dest);
            vis.visit_rvalue(src);
        }

        StmtKind::Call { fun, ret, args } => {
            vis.visit_operand(fun);
            vis.visit_access(ret);
            for ele in args {
                vis.visit_operand(ele);
            }
        }

        StmtKind::CheckCond(op) => vis.visit_operand(op),

        StmtKind::LocalLive(..) => (),
    }
}

pub fn visit_operand<'vis, V>(vis: &mut V, op: &mut Operand<'vis>)
where
    V: PillVisitor<'vis> + ?Sized,
{
    match op {
        Operand::Imm(..) => (),
        Operand::Use(acc) => vis.visit_access(acc),
    }
}

pub fn visit_access<'vis, V>(vis: &mut V, access: &mut Access<'vis>)
where
    V: PillVisitor<'vis> + ?Sized,
{
    let mut coll: Vec<AccessKind<'vis>> = access.modifs().to_vec();
    for ele in &mut coll {
        match ele {
            AccessKind::Index(op) => vis.visit_operand(op),

            AccessKind::Field(..) | AccessKind::Deref => (),
        }
    }

    access.modifs = vis.cx().arena().alloc_from_iter(coll);
}
