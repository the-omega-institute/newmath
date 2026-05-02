import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryLedgerPolicy_empty_raw_iff {source : BHist -> Prop} {visible : BHist} :
    OptionHistoryLedgerPolicy source BHist.Empty visible ↔ hsame visible BHist.Empty := by
  constructor
  · intro ledger
    exact hsame_symm ledger.right
  · intro sameVisible
    exact And.intro (Or.inl (hsame_refl BHist.Empty)) (hsame_symm sameVisible)

end BEDC.Derived.OptionUp
