import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatHistoryClassifier_continuation_result_FieldSingletonClassifier_absurd
    {d d' e e' r r' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> Cont d e r -> Cont d' e' r' ->
      FieldSingletonClassifier r r' -> False := by
  intro classifiedD classifiedE contR _contR' singleton
  have ePositive : PositiveUnaryDenominator e :=
    RatHistoryCarrier_iff_positive_denominator.mp classifiedE.left
  have eUnary : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty ePositive).left
  have canonicalCarrier : RatHistoryCarrier (append d e) :=
    RatHistoryCarrier_append_unary_denominator_closed classifiedD.left eUnary
  have sameCanonicalResult : hsame (append d e) r :=
    cont_deterministic (cont_intro (h := d) (k := e) rfl) contR
  have resultCarrier : RatHistoryCarrier r :=
    RatHistoryCarrier_hsame_transport sameCanonicalResult canonicalCarrier
  exact RatHistoryCarrier_not_empty resultCarrier singleton.left

end BEDC.Derived.FieldUp
