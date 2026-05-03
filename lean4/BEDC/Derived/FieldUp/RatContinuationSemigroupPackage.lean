import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_semigroup_package :
    (forall {d e f de ef left right : BHist}, RatHistoryCarrier d ->
      RatHistoryCarrier e -> RatHistoryCarrier f -> Cont d e de -> Cont e f ef ->
        Cont de f left -> Cont d ef right ->
          RatHistoryCarrier de /\ RatHistoryCarrier ef /\ RatHistoryCarrier left /\
            RatHistoryCarrier right /\ RatHistoryClassifier left right) /\
    (forall {d d' u u' r s : BHist}, RatHistoryClassifier d d' ->
      UnaryHistory u -> UnaryHistory u' -> hsame u u' -> Cont d u r ->
        Cont d' u' s -> RatHistoryClassifier r s) /\
    (forall {d d' e r r' : BHist}, RatHistoryClassifier d d' -> RatHistoryCarrier e ->
      Cont d e r -> Cont d' e r' -> RatHistoryClassifier r r') /\
    (forall {rho v u u' r s : BHist}, RatHistoryLedgerPolicy rho v ->
      UnaryHistory u -> UnaryHistory u' -> hsame u u' -> Cont rho u r ->
        Cont v u' s -> RatHistoryLedgerPolicy r s) /\
    (forall {u : BHist}, RatHistoryCarrier u ->
      (forall {d r : BHist}, RatHistoryCarrier d -> Cont d u r ->
        RatHistoryClassifier r d) -> False) := by
  constructor
  · intro d e f de ef left right carrierD carrierE carrierF contDE contEF contLeft
      contRight
    have laws :=
      field_rat_denominator_continuation_semigroup_laws carrierD carrierE carrierF
        contDE contEF contLeft contRight
    exact ⟨laws.left, laws.right.left, laws.right.right.left, laws.right.right.right.left,
      ⟨laws.right.right.left, laws.right.right.right.left,
        laws.right.right.right.right⟩⟩
  · constructor
    · intro d d' u u' r s classified unaryU unaryU' sameUU' contDU contD'U'
      exact RatHistoryClassifier_matching_continuation_closed classified unaryU unaryU'
        sameUU' contDU contD'U'
    · constructor
      · intro d d' e r r' classified carrierE contDE contD'E
        exact RatHistoryClassifier_continuation_right_closed classified carrierE contDE contD'E
      · constructor
        · intro rho v u u' r s ledger unaryU _unaryU' sameUU' contRU contVU'
          exact RatHistoryLedgerPolicy_continuation_closed ledger unaryU sameUU' contRU
            contVU'
        · intro u carrierU rightUnit
          exact field_rat_denominator_continuation_no_internal_unit carrierU rightUnit

end BEDC.Derived.FieldUp
