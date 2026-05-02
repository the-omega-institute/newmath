import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryCarrier_e1_source_iff {source : BHist -> Prop} {h : BHist} :
    OptionHistoryCarrier source (BHist.e1 h) <-> source (BHist.e1 h) := by
  constructor
  · intro carrier
    cases carrier with
    | inl emptyCase =>
        exact False.elim (not_hsame_e1_empty emptyCase)
    | inr sourceCase =>
        exact sourceCase
  · intro sourceCase
    exact Or.inr sourceCase

end BEDC.Derived.OptionUp
