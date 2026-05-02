import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatHistoryCarrier_continuation_closed {d e r : BHist} :
    BEDC.Derived.RatUp.RatHistoryCarrier d ->
      BEDC.Derived.RatUp.RatHistoryCarrier e ->
        Cont d e r -> BEDC.Derived.RatUp.RatHistoryCarrier r := by
  intro carrierD carrierE continuation
  have positiveE : PositiveUnaryDenominator e :=
    RatHistoryCarrier_iff_positive_denominator.mp carrierE
  have unaryE : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveE).left
  have appendCarrier : BEDC.Derived.RatUp.RatHistoryCarrier (append d e) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierD unaryE
  cases continuation
  exact appendCarrier

theorem RatHistoryClassifier_continuation_right_closed {d d' e r r' : BHist} :
    BEDC.Derived.RatUp.RatHistoryClassifier d d' ->
      BEDC.Derived.RatUp.RatHistoryCarrier e ->
        Cont d e r -> Cont d' e r' ->
          BEDC.Derived.RatUp.RatHistoryClassifier r r' := by
  intro classified carrierE leftContinuation rightContinuation
  have carrierR : BEDC.Derived.RatUp.RatHistoryCarrier r :=
    RatHistoryCarrier_continuation_closed classified.left carrierE leftContinuation
  have carrierR' : BEDC.Derived.RatUp.RatHistoryCarrier r' :=
    RatHistoryCarrier_continuation_closed classified.right.left carrierE rightContinuation
  have sameResult : hsame r r' :=
    cont_respects_hsame classified.right.right (hsame_refl e)
      leftContinuation rightContinuation
  exact ⟨carrierR, carrierR', sameResult⟩

end BEDC.Derived.FieldUp
