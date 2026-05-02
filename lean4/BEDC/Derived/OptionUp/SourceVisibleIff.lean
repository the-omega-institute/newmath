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

theorem OptionHistoryLedgerPolicy_visible_source_exactness {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {raw visible : BHist} :
    source visible -> (OptionHistoryLedgerPolicy source raw visible <-> source raw ∧
      hsame raw visible) := by
  intro visibleSource
  constructor
  · intro ledger
    cases ledger with
    | intro rawCarrier sameRawVisible =>
        constructor
        · cases rawCarrier with
          | inl rawEmpty =>
              exact False.elim
                (sourceExcludesEmpty visible visibleSource
                  (hsame_trans (hsame_symm sameRawVisible) rawEmpty))
          | inr rawSource =>
              exact rawSource
        · exact sameRawVisible
  · intro rawData
    exact And.intro (Or.inr rawData.left) rawData.right

end BEDC.Derived.OptionUp
