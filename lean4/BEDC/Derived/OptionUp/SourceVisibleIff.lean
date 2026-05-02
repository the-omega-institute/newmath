import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryLedgerPolicy_source_visible_iff {source : BHist -> Prop}
    (source_transport : forall {h k : BHist}, hsame h k -> source h -> source k)
    {raw visible : BHist} :
    OptionHistoryLedgerPolicy source raw visible -> (source raw <-> source visible) := by
  intro ledger
  constructor
  · intro rawSource
    exact source_transport ledger.right rawSource
  · intro visibleSource
    exact source_transport (hsame_symm ledger.right) visibleSource

end BEDC.Derived.OptionUp
