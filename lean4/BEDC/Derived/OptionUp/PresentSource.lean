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

theorem OptionHistoryClassifier_e1_left_source_iff {source : BHist → Prop}
    {tail k : BHist} :
    OptionHistoryClassifier source (BHist.e1 tail) k ↔
      source (BHist.e1 tail) ∧ OptionHistoryCarrier source k ∧
        hsame (BHist.e1 tail) k := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierLeft rest =>
        cases rest with
        | intro carrierRight sameEndpoint =>
            exact And.intro
              (OptionHistoryCarrier_e1_source_iff.mp carrierLeft)
              (And.intro carrierRight sameEndpoint)
  · intro data
    cases data with
    | intro sourceLeft rest =>
        cases rest with
        | intro carrierRight sameEndpoint =>
            exact And.intro (Or.inr sourceLeft) (And.intro carrierRight sameEndpoint)

end BEDC.Derived.OptionUp
