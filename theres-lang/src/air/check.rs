use std::borrow::Cow;

use crate::{
    air::{
        def::DefId,
        node::{Block, Thing, ThingKind, Universe},
        visitor::AirVisitor,
    },
    errors::{Phase, TheresError},
    session::Session,
    types::ty::{FnSig, Ty},
};

use crate::symbols::SymbolId;

#[derive(Debug)]
pub enum MainError<'cx> {
    WrongRetType { ty: Ty<'cx> },
    WrongSignature { sig: FnSig<'cx> },
}

struct MainCheck<'cx> {
    cx: &'cx Session<'cx>,
    result: Option<DefId>,
}

impl<'air> AirVisitor<'air> for MainCheck<'_> {
    type Result = ();

    fn visit_block(&mut self, _: &'air Block<'air>) -> Self::Result {}

    fn visit_thing(&mut self, thing: &'air Thing<'air>) -> Self::Result {
        if let ThingKind::Fn { name, sig } = thing.kind
            && name.interned == SymbolId::main()
        {
            let typed_sig = self.cx.fn_sig_for(thing.def_id);

            if !typed_sig.output.is_nil() {
                self.cx.diag().emit_err(
                    MainError::WrongRetType {
                        ty: typed_sig.output,
                    },
                    sig.span,
                );
            }

            if !typed_sig.inputs.is_empty() {
                self.cx
                    .diag()
                    .emit_err(MainError::WrongSignature { sig: typed_sig }, sig.span);
            }

            self.result = Some(thing.def_id);
        }
    }
}

pub fn check_for_main<'cx>(cx: &'cx Session<'cx>, universe: &Universe<'cx>) -> Option<DefId> {
    let mut checker = MainCheck { cx, result: None };

    checker.visit_universe(universe);
    checker.result
}

impl TheresError for MainError<'_> {
    fn phase() -> Phase {
        Phase::TypeCk
    }

    fn message(&self) -> Cow<'static, str> {
        match self {
            Self::WrongRetType { ty } => {
                format!("`main` has an incorrect return type ({ty}), consider using `nil`")
            }
            Self::WrongSignature { sig } => {
                format!("`main`'s signature should be fun() => nil, while it's {sig}")
            }
        }
        .into()
    }
}
