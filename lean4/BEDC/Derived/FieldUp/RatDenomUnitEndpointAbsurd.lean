import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RatDenomUnitCarrier_e0_absurd {tail : BHist} :
    RatDenomUnitCarrier (BHist.e0 tail) -> False := by
  intro carrier
  cases carrier with
  | inl emptyBranch =>
      exact not_hsame_e0_empty emptyBranch
  | inr ratBranch =>
      exact RatHistoryCarrier_e0_absurd ratBranch

theorem RatDenomUnitClassifier_e1_empty_absurd {d : BHist} :
    (RatDenomUnitClassifier (BHist.e1 d) BHist.Empty -> False) ∧
      (RatDenomUnitClassifier BHist.Empty (BHist.e1 d) -> False) := by
  constructor
  · intro classified
    exact not_hsame_e1_empty classified.right.right
  · intro classified
    exact not_hsame_emp_e1 classified.right.right

end BEDC.Derived.FieldUp
