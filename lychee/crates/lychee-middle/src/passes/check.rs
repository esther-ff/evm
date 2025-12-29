use std::borrow::Cow;

use crate::session::Session;
use crate::typing::ty::{FnSig, Ty};
use lychee_air::node::{Block, Thing, ThingKind, Universe};
use lychee_air::visitor::AirVisitor;
use lychee_util::def::DefId;
use lychee_util::errors::TheresError;

use lychee_util::symbols::SymbolId;

#[derive(Debug, Clone, Copy)]
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
    fn message(&self) -> Cow<'static, str> {
        match self {
            Self::WrongRetType { ty } => {
                format!("The return type of `main` is incorrect return type ({ty}), consider using `nil`")
            }
            Self::WrongSignature { sig } => {
                format!("the signature of `main` should be fun() => nil, while it's {sig}")
            }
        }
        .into()
    }
}
