import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryCarrier_e0_source_iff {source : BHist → Prop} {tail : BHist} :
    OptionHistoryCarrier source (BHist.e0 tail) ↔ source (BHist.e0 tail) := by
  constructor
  · intro carrier
    cases carrier with
    | inl emptyCase =>
        exact False.elim (not_hsame_e0_empty emptyCase)
    | inr sourceCase =>
        exact sourceCase
  · intro sourceCase
    exact Or.inr sourceCase

theorem OptionHistoryClassifier_e0_left_source_iff {source : BHist → Prop}
    {tail k : BHist} :
    OptionHistoryClassifier source (BHist.e0 tail) k ↔
      source (BHist.e0 tail) ∧ OptionHistoryCarrier source k ∧
        hsame (BHist.e0 tail) k := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierLeft rest =>
        cases rest with
        | intro carrierRight sameEndpoint =>
            exact And.intro
              (OptionHistoryCarrier_e0_source_iff.mp carrierLeft)
              (And.intro carrierRight sameEndpoint)
  · intro data
    cases data with
    | intro sourceLeft rest =>
        cases rest with
        | intro carrierRight sameEndpoint =>
            exact And.intro (Or.inr sourceLeft) (And.intro carrierRight sameEndpoint)

end BEDC.Derived.OptionUp
