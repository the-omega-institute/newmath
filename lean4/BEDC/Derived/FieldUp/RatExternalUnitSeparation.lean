import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_external_unit_separation_package {u : BHist} :
    (((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ↔
        hsame u BHist.Empty) ∧
      ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ↔
        hsame u BHist.Empty) ∧
      (RatHistoryCarrier u ->
        ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
          False) ∧
          ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
            False))) := by
  constructor
  · exact field_rat_denominator_continuation_right_unit_law_endpoint_empty_iff
  · constructor
    · exact field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff
    · intro carrierU
      constructor
      · intro rightUnit
        exact field_rat_denominator_continuation_no_internal_unit carrierU rightUnit
      · intro leftUnit
        exact field_rat_denominator_continuation_no_internal_left_unit carrierU leftUnit

theorem field_rat_denominator_external_unit_endpoint_disjunction_unique {u v : BHist} :
    ((forall {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) \/
        (forall {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d)) ->
      ((forall {d r : BHist}, RatHistoryCarrier d -> Cont d v r -> RatHistoryClassifier r d) \/
        (forall {d r : BHist}, RatHistoryCarrier d -> Cont v d r -> RatHistoryClassifier r d)) ->
        hsame u v := by
  intro endpointU endpointV
  cases endpointU with
  | inl rightU =>
      cases endpointV with
      | inl rightV =>
          exact field_rat_denominator_continuation_unit_endpoint_unique.left rightU rightV
      | inr leftV =>
          exact field_rat_denominator_continuation_unit_endpoint_unique.right.right rightU leftV
  | inr leftU =>
      cases endpointV with
      | inl rightV =>
          exact hsame_symm
            (field_rat_denominator_continuation_unit_endpoint_unique.right.right rightV leftU)
      | inr leftV =>
          exact field_rat_denominator_continuation_unit_endpoint_unique.right.left leftU leftV

end BEDC.Derived.FieldUp
