import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryCarrier_absent_not_source_iff {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h : BHist} :
    OptionHistoryCarrier source h -> (hsame h BHist.Empty <-> (source h -> False)) := by
  intro carrier
  constructor
  · intro emptyCase sourceCase
    exact sourceExcludesEmpty h sourceCase emptyCase
  · intro notSource
    cases carrier with
    | inl emptyCase =>
        exact emptyCase
    | inr sourceCase =>
        exact False.elim (notSource sourceCase)

end BEDC.Derived.OptionUp
