import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryCarrier_e0_absurd {S : BHist → Prop} {tail : BHist} :
    TaggedOptionHistoryCarrier S (BHist.e0 tail) → False := by
  intro carrier
  cases carrier with
  | inl absent =>
      exact not_hsame_e0_empty absent
  | inr present =>
      cases present with
      | intro a data =>
          cases data with
          | intro _source samePresent =>
              exact not_hsame_e0_e1 samePresent

end BEDC.Derived.OptionUp
