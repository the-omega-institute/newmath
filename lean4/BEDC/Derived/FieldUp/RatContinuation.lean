import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.FKernel.Cont.Cancellation

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

theorem RatHistoryCarrier_continuation_semigroup_laws {d e f de ef left right : BHist} :
    RatHistoryCarrier d -> RatHistoryCarrier e -> RatHistoryCarrier f -> Cont d e de ->
      Cont e f ef -> Cont de f left -> Cont d ef right ->
        RatHistoryCarrier de ∧ RatHistoryCarrier ef ∧ RatHistoryCarrier left ∧
          RatHistoryCarrier right ∧ hsame left right := by
  intro carrierD carrierE carrierF deContinuation efContinuation leftContinuation rightContinuation
  have carrierDE : RatHistoryCarrier de :=
    RatHistoryCarrier_continuation_closed carrierD carrierE deContinuation
  have carrierEF : RatHistoryCarrier ef :=
    RatHistoryCarrier_continuation_closed carrierE carrierF efContinuation
  have carrierLeft : RatHistoryCarrier left :=
    RatHistoryCarrier_continuation_closed carrierDE carrierF leftContinuation
  have carrierRight : RatHistoryCarrier right :=
    RatHistoryCarrier_continuation_closed carrierD carrierEF rightContinuation
  have sameResults : hsame left right :=
    cont_assoc_hsame deContinuation leftContinuation efContinuation rightContinuation
  exact And.intro carrierDE
    (And.intro carrierEF
      (And.intro carrierLeft (And.intro carrierRight sameResults)))

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

theorem RatHistoryClassifier_matching_continuation_closed {d e u v r s : BHist} :
    RatHistoryClassifier d e -> UnaryHistory u -> UnaryHistory v -> hsame u v ->
      Cont d u r -> Cont e v s -> RatHistoryClassifier r s := by
  intro classified unaryU _unaryV sameUV leftContinuation rightContinuation
  have appendedClassified :
      RatHistoryClassifier (append d u) (append e v) :=
    RatHistoryClassifier_append_unary_denominator_closed classified unaryU sameUV
  have sameLeft : hsame (append d u) r := by
    exact leftContinuation.symm
  have sameRight : hsame (append e v) s := by
    exact rightContinuation.symm
  exact RatHistoryClassifier_hsame_transport sameLeft sameRight appendedClassified

theorem field_rat_denominator_continuation_common_context_cancel
    {p q d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory q -> RatHistoryCarrier d -> RatHistoryCarrier e ->
      Cont p d pd -> Cont p e pe -> Cont pd q left -> Cont pe q right ->
        RatHistoryClassifier left right -> RatHistoryClassifier d e := by
  intro _prefixUnary _suffixUnary carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix
    classified
  have sameDE : hsame d e :=
    cont_cancel_common_context leftPrefix leftSuffix rightPrefix rightSuffix classified.right.right
  exact ⟨carrierD, carrierE, sameDE⟩

theorem field_rat_denominator_continuation_classifier_assoc_congruence
    {d d' e e' f f' de de' ef ef' left left' right right' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> RatHistoryClassifier f f' ->
      Cont d e de -> Cont d' e' de' -> Cont e f ef -> Cont e' f' ef' ->
        Cont de f left -> Cont de' f' left' -> Cont d ef right -> Cont d' ef' right' ->
          RatHistoryClassifier left left' ∧ RatHistoryClassifier right right' ∧
            hsame left right ∧ hsame left' right' := by
  intro classifiedD classifiedE classifiedF contDE contD'E' contEF contE'F' contLeft
    contLeft' contRight contRight'
  have unaryE : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedE.left)).left
  have unaryE' : UnaryHistory e' :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedE.right.left)).left
  have unaryF : UnaryHistory f :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedF.left)).left
  have unaryF' : UnaryHistory f' :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedF.right.left)).left
  have classifiedDE : RatHistoryClassifier de de' :=
    RatHistoryClassifier_matching_continuation_closed classifiedD unaryE unaryE'
      classifiedE.right.right contDE contD'E'
  have classifiedEF : RatHistoryClassifier ef ef' :=
    RatHistoryClassifier_matching_continuation_closed classifiedE unaryF unaryF'
      classifiedF.right.right contEF contE'F'
  have classifiedLeft : RatHistoryClassifier left left' :=
    RatHistoryClassifier_matching_continuation_closed classifiedDE unaryF unaryF'
      classifiedF.right.right contLeft contLeft'
  have unaryEF : UnaryHistory ef :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedEF.left)).left
  have unaryEF' : UnaryHistory ef' :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedEF.right.left)).left
  have classifiedRight : RatHistoryClassifier right right' :=
    RatHistoryClassifier_matching_continuation_closed classifiedD unaryEF unaryEF'
      classifiedEF.right.right contRight contRight'
  have unprimed :=
    field_rat_denominator_continuation_semigroup_laws classifiedD.left classifiedE.left
      classifiedF.left contDE contEF contLeft contRight
  have primed :=
    field_rat_denominator_continuation_semigroup_laws classifiedD.right.left classifiedE.right.left
      classifiedF.right.left contD'E' contE'F' contLeft' contRight'
  exact ⟨classifiedLeft, classifiedRight, unprimed.right.right.right.right,
    primed.right.right.right.right⟩

end BEDC.Derived.FieldUp
