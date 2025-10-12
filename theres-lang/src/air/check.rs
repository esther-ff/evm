use crate::{
    air::{
        def::DefId,
        node::{Block, Thing, ThingKind, Universe},
        visitor::AirVisitor,
    },
    session::{Session, SymbolId},
    types::ty::{FnSig, Ty},
};

pub enum MainError<'cx> {
    NoMain,
    WrongRetType { ty: Ty<'cx> },
    WrongSignature { sig: FnSig<'cx> },
}

struct MainCheck<'cx> {
    cx: &'cx Session<'cx>,
    result: Result<DefId, MainError<'cx>>,
}

impl<'air> AirVisitor<'air> for MainCheck<'_> {
    type Result = ();

    fn visit_block(&mut self, _: &'air Block<'air>) -> Self::Result {}

    fn visit_thing(&mut self, thing: &'air Thing<'air>) -> Self::Result {
        if let ThingKind::Fn { name, sig: _ } = thing.kind
            && name.interned == SymbolId::main()
        {
            let typed_sig = self.cx.fn_sig_for(thing.def_id);

            if !typed_sig.output.is_nil() {
                self.result = Err(MainError::WrongRetType {
                    ty: typed_sig.output,
                });
                return;
            }

            if !typed_sig.inputs.is_empty() {
                self.result = Err(MainError::WrongSignature { sig: typed_sig });
                return;
            }

            self.result = Ok(thing.def_id);
        }
    }
}

pub fn check_for_main<'cx>(
    cx: &'cx Session<'cx>,
    universe: &Universe<'cx>,
) -> Result<DefId, MainError<'cx>> {
    let mut checker = MainCheck {
        cx,
        result: Err(MainError::NoMain),
    };

    checker.visit_universe(universe);
    checker.result
}
