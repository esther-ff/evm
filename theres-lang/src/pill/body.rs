mod private {
    crate::newtyped_index!(AltarId, AltarMap, AltarVec, _Useless);
    pub type Altars<'il> = AltarVec<super::AltarData<'il>>;

    impl AltarId {
        pub const NIL_ALTAR: Self = AltarId::new(u32::MAX - 1);

        pub fn is_nil_altar(self) -> bool {
            self == Self::NIL_ALTAR
        }
    }
}

use crate::pill::instr::{Instr, InstrStream, Operand};
use crate::span::Span;
use crate::symbols::SymbolId;
use crate::types::fun_cx::FieldId;
use crate::types::ty::Ty;

pub use private::{AltarId, Altars};

use std::fmt::Debug;
use std::io::{self, Write};

crate::newtyped_index!(LabelId, LabelMap, LabelVec, LabelSlice);

#[derive(Debug, Clone)]
pub struct AltarData<'il> {
    ty: Ty<'il>,
    projs: Vec<Proj>,
}

#[derive(Debug, Clone, Copy)]
pub enum Proj {
    Field { field: FieldId, source: AltarId },
    Index(Operand),
}

impl<'il> AltarData<'il> {
    pub fn new(ty: Ty<'il>) -> Self {
        Self { ty, projs: vec![] }
    }

    pub fn projs(&self) -> &[Proj] {
        &self.projs
    }

    pub fn push_proj(&mut self, val: Proj) {
        self.projs.push(val);
    }
}

pub struct IrFunc<'il> {
    name: SymbolId,
    span: Span,
    altars: Altars<'il>,
    instructions: InstrStream<'il>,
    labels: LabelVec<usize>,
}

impl<'il> IrFunc<'il> {
    pub fn new(
        name: SymbolId,
        span: Span,
        altars: Altars<'il>,
        instructions: InstrStream<'il>,
        labels: LabelVec<usize>,
    ) -> Self {
        Self {
            name,
            span,
            altars,
            instructions,
            labels,
        }
    }

    pub fn altars(&self) -> &[AltarData<'il>] {
        &self.altars
    }

    pub fn name(&self) -> SymbolId {
        self.name
    }

    pub fn insts(&self) -> &[Instr<'il>] {
        self.instructions.tac()
    }

    pub fn labels(&self) -> &[usize] {
        &self.labels
    }

    pub fn pretty_print<O: Write>(&self, w: &mut O) -> io::Result<()> {
        writeln!(w, ".fn {}() :: <anon>", self.name.get_interned())?;

        for (ix, altar) in self.altars().iter().enumerate() {
            writeln!(w, "    _{ix}: {altar:?}")?;
        }

        writeln!(w)?;

        for (ix, inst) in self.instructions.tac().iter().enumerate() {
            if let Some(idx) = self.labels.iter().position(|&x| x == ix) {
                writeln!(w, "    label({idx}):")?;
            }

            writeln!(w, "      {inst}")?;
        }

        Ok(())
    }
}
