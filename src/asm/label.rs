use crate::object::write::SymbolId;

#[derive(Eq, Ord, Hash, Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct LabelId(pub(crate) usize);

#[derive(Copy, Clone, Debug)]
pub struct Label {
    pub sym: SymbolId,
}

