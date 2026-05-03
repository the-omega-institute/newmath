import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_visible_left_unit_law_absurd {u : BHist} :
    ((∃ tail : BHist, hsame u (BHist.e0 tail)) ∨
        (∃ tail : BHist, hsame u (BHist.e1 tail))) ->
      (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
        False := by
  intro visible leftUnit
  have endpointEmpty : hsame u BHist.Empty :=
    field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff.mp leftUnit
  cases visible with
  | inl zeroVisible =>
      cases zeroVisible with
      | intro tail sameU =>
          exact not_hsame_e0_empty (hsame_trans (hsame_symm sameU) endpointEmpty)
  | inr oneVisible =>
      cases oneVisible with
      | intro tail sameU =>
          exact not_hsame_e1_empty (hsame_trans (hsame_symm sameU) endpointEmpty)

end BEDC.Derived.FieldUp
