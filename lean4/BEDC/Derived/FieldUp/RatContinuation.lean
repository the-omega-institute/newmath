import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier

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

theorem field_rat_denominator_continuation_semigroup_laws {d e f de ef left right : BHist} :
    RatHistoryCarrier d -> RatHistoryCarrier e -> RatHistoryCarrier f -> Cont d e de ->
      Cont e f ef -> Cont de f left -> Cont d ef right ->
        RatHistoryCarrier de ∧ RatHistoryCarrier ef ∧ RatHistoryCarrier left ∧
          RatHistoryCarrier right ∧ hsame left right := by
  intro carrierD carrierE carrierF contDE contEF contLeft contRight
  have carrierDE : RatHistoryCarrier de :=
    RatHistoryCarrier_continuation_closed carrierD carrierE contDE
  have carrierEF : RatHistoryCarrier ef :=
    RatHistoryCarrier_continuation_closed carrierE carrierF contEF
  have carrierLeft : RatHistoryCarrier left :=
    RatHistoryCarrier_continuation_closed carrierDE carrierF contLeft
  have carrierRight : RatHistoryCarrier right :=
    RatHistoryCarrier_continuation_closed carrierD carrierEF contRight
  have sameResults : hsame left right :=
    cont_assoc_hsame contDE contLeft contEF contRight
  exact ⟨carrierDE, carrierEF, carrierLeft, carrierRight, sameResults⟩

theorem RatHistoryLedgerPolicy_continuation_closed {raw visible tailRaw tailVisible r s : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory tailRaw -> hsame tailRaw tailVisible ->
      Cont raw tailRaw r -> Cont visible tailVisible s -> RatHistoryLedgerPolicy r s := by
  intro ledger tailRawUnary tailSame rawContinuation visibleContinuation
  have canonicalLedger :
      RatHistoryLedgerPolicy (append raw tailRaw) (append visible tailVisible) :=
    RatHistoryLedgerPolicy_append_unary_denominator_closed ledger tailRawUnary tailSame
  have rawSame : hsame (append raw tailRaw) r :=
    cont_deterministic
      (cont_intro (h := raw) (k := tailRaw) (r := append raw tailRaw) rfl)
      rawContinuation
  have visibleSame : hsame (append visible tailVisible) s :=
    cont_deterministic
      (cont_intro (h := visible) (k := tailVisible) (r := append visible tailVisible) rfl)
      visibleContinuation
  exact RatHistoryLedgerPolicy_hsame_transport canonicalLedger rawSame visibleSame

end BEDC.Derived.FieldUp
