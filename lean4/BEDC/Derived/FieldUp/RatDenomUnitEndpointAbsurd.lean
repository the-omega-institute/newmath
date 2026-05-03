import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitCarrier_e0_absurd {tail : BHist} :
    RatDenomUnitCarrier (BHist.e0 tail) -> False := by
  intro carrier
  cases carrier with
  | inl emptyBranch =>
      exact not_hsame_e0_empty emptyBranch
  | inr ratBranch =>
      exact RatHistoryCarrier_e0_absurd ratBranch

theorem RatDenomUnitClassifier_empty_endpoint_iff {h : BHist} :
    (RatDenomUnitClassifier BHist.Empty h <-> hsame h BHist.Empty) ∧
      (RatDenomUnitClassifier h BHist.Empty <-> hsame h BHist.Empty) := by
  constructor
  · constructor
    · intro classified
      exact hsame_symm classified.right.right
    · intro sameEmpty
      exact And.intro (Or.inl (hsame_refl BHist.Empty))
        (And.intro (Or.inl sameEmpty) (hsame_symm sameEmpty))
  · constructor
    · intro classified
      exact classified.right.right
    · intro sameEmpty
      exact And.intro (Or.inl sameEmpty)
        (And.intro (Or.inl (hsame_refl BHist.Empty)) sameEmpty)

theorem RatDenomUnitCarrier_append_e0_absurd {h k tail : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k -> hsame (append h k) (BHist.e0 tail) ->
      False := by
  intro carrierH carrierK sameEndpoint
  have productCarrier : RatDenomUnitCarrier (append h k) :=
    RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
  exact RatDenomUnitCarrier_e0_absurd
    (RatDenomUnitCarrier_hsame_transport sameEndpoint productCarrier)

theorem RatDenomUnitClassifier_e1_empty_absurd {d : BHist} :
    (RatDenomUnitClassifier (BHist.e1 d) BHist.Empty -> False) ∧
      (RatDenomUnitClassifier BHist.Empty (BHist.e1 d) -> False) := by
  constructor
  · intro classified
    exact not_hsame_e1_empty classified.right.right
  · intro classified
    exact not_hsame_emp_e1 classified.right.right

end BEDC.Derived.FieldUp
