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

end BEDC.Derived.FieldUp
