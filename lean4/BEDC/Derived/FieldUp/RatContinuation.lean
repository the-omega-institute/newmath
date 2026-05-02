import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.DenominatorContext
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary.Commutativity

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

theorem RatHistoryCarrier_continuation_result_not_empty {d e r : BHist} :
    RatHistoryCarrier d -> RatHistoryCarrier e -> Cont d e r ->
      hsame r BHist.Empty -> False := by
  intro carrierD carrierE continuation resultEmpty
  have carrierR : RatHistoryCarrier r :=
    RatHistoryCarrier_continuation_closed carrierD carrierE continuation
  exact RatHistoryCarrier_not_empty carrierR resultEmpty

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

theorem field_rat_denominator_continuation_commutative_classifier {d e r s : BHist} :
    RatHistoryCarrier d -> RatHistoryCarrier e -> Cont d e r -> Cont e d s ->
      RatHistoryClassifier r s := by
  intro carrierD carrierE leftContinuation rightContinuation
  have carrierR : RatHistoryCarrier r :=
    RatHistoryCarrier_continuation_closed carrierD carrierE leftContinuation
  have carrierS : RatHistoryCarrier s :=
    RatHistoryCarrier_continuation_closed carrierE carrierD rightContinuation
  have unaryD : UnaryHistory d :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrierD)).left
  have unaryE : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrierE)).left
  have sameRS : hsame r s :=
    unary_continuation_commutativity unaryD unaryE leftContinuation rightContinuation
  exact ⟨carrierR, carrierS, sameRS⟩

theorem field_rat_denominator_continuation_no_internal_left_unit {u : BHist} :
    RatHistoryCarrier u ->
      (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
        False := by
  intro carrierU classifyLeftUnit
  have carrierD : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have displayed : Cont u (BHist.e1 BHist.Empty) (append u (BHist.e1 BHist.Empty)) :=
    cont_intro rfl
  have classified :
      RatHistoryClassifier (append u (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) :=
    classifyLeftUnit carrierD displayed
  have internalLeftUnit : Cont u (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport displayed classified.right.right
  exact RatHistoryCarrier_not_empty carrierU (cont_left_unit_unique internalLeftUnit)

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

theorem field_rat_denominator_append_concrete_instance_laws {d d' e e' f rho v : BHist} :
    RatHistoryCarrier d -> RatHistoryCarrier e -> RatHistoryCarrier f ->
      RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> RatHistoryLedgerPolicy rho v ->
        RatHistoryCarrier (append d e) ∧
          RatHistoryClassifier (append d e) (append e d) ∧
            RatHistoryClassifier (append (append d e) f) (append d (append e f)) ∧
              RatHistoryClassifier (append d e) (append d' e') ∧
                RatHistoryLedgerPolicy (append rho e) (append v e') := by
  intro carrierD carrierE carrierF classifiedD classifiedE ledger
  have unaryD : UnaryHistory d :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrierD)).left
  have unaryE : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrierE)).left
  have unaryF : UnaryHistory f :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrierF)).left
  have carrierDE : RatHistoryCarrier (append d e) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierD unaryE
  have carrierED : RatHistoryCarrier (append e d) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierE unaryD
  have commClassifier : RatHistoryClassifier (append d e) (append e d) :=
    ⟨carrierDE, carrierED, unary_append_comm unaryD unaryE⟩
  have carrierLeft : RatHistoryCarrier (append (append d e) f) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierDE unaryF
  have carrierEF : RatHistoryCarrier (append e f) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierE unaryF
  have carrierRight : RatHistoryCarrier (append d (append e f)) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierD
      (unary_append_closed unaryE unaryF)
  have assocClassifier :
      RatHistoryClassifier (append (append d e) f) (append d (append e f)) :=
    ⟨carrierLeft, carrierRight, append_assoc d e f⟩
  have congrClassifier : RatHistoryClassifier (append d e) (append d' e') :=
    RatHistoryClassifier_append_unary_denominator_closed classifiedD unaryE classifiedE.right.right
  have ledgerClosed : RatHistoryLedgerPolicy (append rho e) (append v e') :=
    RatHistoryLedgerPolicy_append_unary_denominator_closed ledger unaryE classifiedE.right.right
  exact ⟨carrierDE, commClassifier, assocClassifier, congrClassifier, ledgerClosed⟩

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

theorem RatHistoryLedgerPolicy_continuation_results_not_empty
    {raw visible tailRaw tailVisible r s : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory tailRaw -> hsame tailRaw tailVisible ->
      Cont raw tailRaw r -> Cont visible tailVisible s ->
        (hsame r BHist.Empty -> False) ∧ (hsame s BHist.Empty -> False) := by
  intro ledger tailRawUnary tailSame rawContinuation visibleContinuation
  have resultLedger : RatHistoryLedgerPolicy r s :=
    RatHistoryLedgerPolicy_continuation_closed ledger tailRawUnary tailSame rawContinuation
      visibleContinuation
  constructor
  · intro rawEmpty
    exact RatHistoryCarrier_not_empty resultLedger.left rawEmpty
  · intro visibleEmpty
    exact RatHistoryCarrier_not_empty (RatHistoryLedgerPolicy_visible_carrier resultLedger)
      visibleEmpty

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

theorem field_rat_denominator_continuation_binary_classifier_congruence
    {d d' e e' r r' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> Cont d e r ->
      Cont d' e' r' -> RatHistoryClassifier r r' := by
  intro classifiedD classifiedE leftContinuation rightContinuation
  have unaryE : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedE.left)).left
  have unaryE' : UnaryHistory e' :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp classifiedE.right.left)).left
  exact RatHistoryClassifier_matching_continuation_closed classifiedD unaryE unaryE'
    classifiedE.right.right leftContinuation rightContinuation

theorem RatHistoryClassifier_continuation_result_not_empty {d d' e e' r r' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> Cont d e r ->
      Cont d' e' r' ->
        (hsame r BHist.Empty -> False) ∧ (hsame r' BHist.Empty -> False) := by
  intro classifiedD classifiedE leftContinuation rightContinuation
  have resultClassified : RatHistoryClassifier r r' :=
    field_rat_denominator_continuation_binary_classifier_congruence classifiedD classifiedE
      leftContinuation rightContinuation
  constructor
  · intro leftEmpty
    exact RatHistoryCarrier_not_empty resultClassified.left leftEmpty
  · intro rightEmpty
    exact RatHistoryCarrier_not_empty resultClassified.right.left rightEmpty

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

theorem field_rat_denominator_continuation_common_context_classifier_exactness
    {p q d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory q -> RatHistoryCarrier d -> RatHistoryCarrier e ->
      Cont p d pd -> Cont p e pe -> Cont pd q left -> Cont pe q right ->
        (RatHistoryClassifier d e <-> RatHistoryClassifier left right) := by
  intro prefixUnary suffixUnary carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix
  constructor
  · intro classified
    have contextClassified :
        RatHistoryClassifier (append p (append d q)) (append p (append e q)) :=
      RatHistoryClassifier_unary_denominator_context_closed classified prefixUnary
        (hsame_refl p) suffixUnary (hsame_refl q)
    have sameLeft : hsame (append p (append d q)) left := by
      cases leftPrefix
      cases leftSuffix
      exact (append_assoc p d q).symm
    have sameRight : hsame (append p (append e q)) right := by
      cases rightPrefix
      cases rightSuffix
      exact (append_assoc p e q).symm
    exact RatHistoryClassifier_hsame_transport sameLeft sameRight contextClassified
  · intro classified
    exact field_rat_denominator_continuation_common_context_cancel prefixUnary suffixUnary
      carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix classified

theorem field_rat_denominator_matched_context_classifier_iff
    {p q d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory q -> RatHistoryCarrier d -> RatHistoryCarrier e ->
      Cont p d pd -> Cont p e pe -> Cont pd q left -> Cont pe q right ->
        (RatHistoryClassifier d e <-> RatHistoryClassifier left right) := by
  exact field_rat_denominator_continuation_common_context_classifier_exactness

theorem field_rat_denominator_continuation_common_context_ledger_closure
    {p p' q q' rho v pr pv left right : BHist} :
    RatHistoryLedgerPolicy rho v -> UnaryHistory p -> UnaryHistory p' -> UnaryHistory q ->
      UnaryHistory q' -> hsame p p' -> hsame q q' -> Cont p rho pr ->
        Cont p' v pv -> Cont pr q left -> Cont pv q' right ->
          RatHistoryLedgerPolicy left right := by
  intro ledger pUnary _p'Unary qUnary _q'Unary sameP sameQ leftPrefix rightPrefix
    leftSuffix rightSuffix
  have canonicalLedger :
      RatHistoryLedgerPolicy (append p (append rho q)) (append p' (append v q')) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed ledger pUnary sameP qUnary sameQ
  have sameLeft : hsame (append p (append rho q)) left := by
    cases leftPrefix
    cases leftSuffix
    exact (append_assoc p rho q).symm
  have sameRight : hsame (append p' (append v q')) right := by
    cases rightPrefix
    cases rightSuffix
    exact (append_assoc p' v q').symm
  exact RatHistoryLedgerPolicy_hsame_transport canonicalLedger sameLeft sameRight

theorem field_rat_denominator_continuation_common_context_exactness_package
    {p q d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory q -> RatHistoryCarrier d -> RatHistoryCarrier e ->
      Cont p d pd -> Cont p e pe -> Cont pd q left -> Cont pe q right ->
        (RatHistoryClassifier left right <-> RatHistoryClassifier d e) /\
          (RatHistoryLedgerPolicy left right <-> RatHistoryLedgerPolicy d e) := by
  intro prefixUnary suffixUnary carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix
  have classifierExact :
      RatHistoryClassifier d e <-> RatHistoryClassifier left right :=
    field_rat_denominator_continuation_common_context_classifier_exactness prefixUnary
      suffixUnary carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix
  have sameLeft : hsame (append p (append d q)) left :=
    (append_assoc p d q).symm.trans
      ((congrArg (fun x => append x q) leftPrefix.symm).trans leftSuffix.symm)
  have sameRight : hsame (append p (append e q)) right :=
    (append_assoc p e q).symm.trans
      ((congrArg (fun x => append x q) rightPrefix.symm).trans rightSuffix.symm)
  constructor
  · constructor
    · intro classified
      exact classifierExact.mpr classified
    · intro classified
      exact classifierExact.mp classified
  · constructor
    · intro ledger
      have classified :
          RatHistoryClassifier d e :=
        field_rat_denominator_continuation_common_context_cancel prefixUnary suffixUnary
          carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix
          (RatHistoryLedgerPolicy_raw_visible_classifier ledger)
      exact ⟨carrierD, classified.right.right⟩
    · intro ledger
      have contextLedger :
          RatHistoryLedgerPolicy (append p (append d q)) (append p (append e q)) :=
        RatHistoryLedgerPolicy_unary_denominator_context_closed ledger prefixUnary
          (hsame_refl p) suffixUnary (hsame_refl q)
      exact RatHistoryLedgerPolicy_hsame_transport contextLedger sameLeft sameRight

theorem field_rat_denominator_hsame_matched_context_classifier_exactness
    {p p' q q' d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory p' -> UnaryHistory q -> UnaryHistory q' -> hsame p p' ->
      hsame q q' -> RatHistoryCarrier d -> RatHistoryCarrier e -> Cont p d pd ->
        Cont p' e pe -> Cont pd q left -> Cont pe q' right ->
          (RatHistoryClassifier d e <-> RatHistoryClassifier left right) := by
  intro prefixUnary _prefixUnary' suffixUnary _suffixUnary' samePrefix sameSuffix carrierD
    carrierE leftPrefix rightPrefix leftSuffix rightSuffix
  cases samePrefix
  cases sameSuffix
  exact field_rat_denominator_continuation_common_context_classifier_exactness prefixUnary
    suffixUnary carrierD carrierE leftPrefix rightPrefix leftSuffix rightSuffix

theorem field_rat_denominator_hsame_matched_context_ledger_exactness
    {p p' q q' d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory p' -> UnaryHistory q -> UnaryHistory q' -> hsame p p' ->
      hsame q q' -> RatHistoryCarrier d -> RatHistoryCarrier e -> Cont p d pd ->
        Cont p' e pe -> Cont pd q left -> Cont pe q' right ->
          (RatHistoryLedgerPolicy d e <-> RatHistoryLedgerPolicy left right) := by
  intro prefixUnary prefixUnary' suffixUnary suffixUnary' samePrefix sameSuffix carrierD
    carrierE leftPrefix rightPrefix leftSuffix rightSuffix
  have classifierExact :
      RatHistoryClassifier d e <-> RatHistoryClassifier left right :=
    field_rat_denominator_hsame_matched_context_classifier_exactness prefixUnary prefixUnary'
      suffixUnary suffixUnary' samePrefix sameSuffix carrierD carrierE leftPrefix rightPrefix
      leftSuffix rightSuffix
  constructor
  · intro ledger
    exact field_rat_denominator_continuation_common_context_ledger_closure ledger prefixUnary
      prefixUnary' suffixUnary suffixUnary' samePrefix sameSuffix leftPrefix rightPrefix
      leftSuffix rightSuffix
  · intro ledger
    have classifiedLeftRight : RatHistoryClassifier left right :=
      RatHistoryLedgerPolicy_raw_visible_classifier ledger
    have classifiedDE : RatHistoryClassifier d e :=
      classifierExact.mpr classifiedLeftRight
    exact ⟨carrierD, classifiedDE.right.right⟩

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

theorem field_rat_denominator_continuation_no_internal_unit {u : BHist} :
    RatHistoryCarrier u ->
      (∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
        False := by
  intro carrierU rightUnitLaw
  have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have canonicalContinuation :
      Cont (BHist.e1 BHist.Empty) u (append (BHist.e1 BHist.Empty) u) :=
    cont_intro rfl
  have classifiedResult :
      RatHistoryClassifier (append (BHist.e1 BHist.Empty) u) (BHist.e1 BHist.Empty) :=
    rightUnitLaw carrierD1 canonicalContinuation
  have collapsedContinuation : Cont (BHist.e1 BHist.Empty) u (BHist.e1 BHist.Empty) :=
    cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
  have unitEmpty : hsame u BHist.Empty :=
    cont_right_unit_unique collapsedContinuation
  exact RatHistoryCarrier_not_empty carrierU unitEmpty

theorem field_rat_denominator_continuation_unit_endpoint_empty {u : BHist} :
    ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
        hsame u BHist.Empty) ∧
      ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
        hsame u BHist.Empty) ∧
      (RatHistoryCarrier u ->
        ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ∨
          (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d)) ->
          False) := by
  have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have rightEndpointEmpty :
      (∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
        hsame u BHist.Empty := by
    intro rightEndpoint
    have canonicalContinuation :
        Cont (BHist.e1 BHist.Empty) u (append (BHist.e1 BHist.Empty) u) :=
      cont_intro rfl
    have classifiedResult :
        RatHistoryClassifier (append (BHist.e1 BHist.Empty) u) (BHist.e1 BHist.Empty) :=
      rightEndpoint carrierD1 canonicalContinuation
    have collapsedContinuation : Cont (BHist.e1 BHist.Empty) u (BHist.e1 BHist.Empty) :=
      cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
    exact cont_right_unit_unique collapsedContinuation
  have leftEndpointEmpty :
      (∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
        hsame u BHist.Empty := by
    intro leftEndpoint
    have canonicalContinuation :
        Cont u (BHist.e1 BHist.Empty) (append u (BHist.e1 BHist.Empty)) :=
      cont_intro rfl
    have classifiedResult :
        RatHistoryClassifier (append u (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) :=
      leftEndpoint carrierD1 canonicalContinuation
    have collapsedContinuation : Cont u (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
      cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
    exact cont_left_unit_unique collapsedContinuation
  exact ⟨rightEndpointEmpty, leftEndpointEmpty, by
    intro carrierU endpointLaw
    cases endpointLaw with
    | inl rightEndpoint =>
        exact RatHistoryCarrier_not_empty carrierU (rightEndpointEmpty rightEndpoint)
    | inr leftEndpoint =>
        exact RatHistoryCarrier_not_empty carrierU (leftEndpointEmpty leftEndpoint)⟩

theorem field_rat_denominator_continuation_right_unit_law_endpoint_empty_iff {u : BHist} :
    ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) <->
      hsame u BHist.Empty) := by
  constructor
  · intro rightUnitLaw
    exact field_rat_denominator_continuation_unit_endpoint_empty.left rightUnitLaw
  · intro endpointEmpty
    intro d r carrierD continuation
    have transportedRightUnit : Cont d u d :=
      cont_hsame_transport (hsame_refl d) (hsame_symm endpointEmpty) (hsame_refl d)
        (cont_right_unit d)
    have sameDR : hsame d r := cont_deterministic transportedRightUnit continuation
    have carrierR : RatHistoryCarrier r :=
      RatHistoryCarrier_hsame_transport sameDR carrierD
    exact And.intro carrierR (And.intro carrierD (hsame_symm sameDR))

theorem field_rat_denominator_continuation_unit_endpoint_unique {u v : BHist} :
    ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
        (∀ {d r : BHist}, RatHistoryCarrier d -> Cont d v r -> RatHistoryClassifier r d) ->
          hsame u v) ∧
      ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ->
        (∀ {d r : BHist}, RatHistoryCarrier d -> Cont v d r -> RatHistoryClassifier r d) ->
          hsame u v) ∧
      ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d) ->
        (∀ {d r : BHist}, RatHistoryCarrier d -> Cont v d r -> RatHistoryClassifier r d) ->
          hsame u v) := by
  constructor
  · intro rightU rightV
    exact hsame_trans
      (field_rat_denominator_continuation_unit_endpoint_empty.left rightU)
      (hsame_symm (field_rat_denominator_continuation_unit_endpoint_empty.left rightV))
  · constructor
    · intro leftU leftV
      exact hsame_trans
        (field_rat_denominator_continuation_unit_endpoint_empty.right.left leftU)
        (hsame_symm (field_rat_denominator_continuation_unit_endpoint_empty.right.left leftV))
    · intro rightU leftV
      exact hsame_trans
        (field_rat_denominator_continuation_unit_endpoint_empty.left rightU)
        (hsame_symm (field_rat_denominator_continuation_unit_endpoint_empty.right.left leftV))

end BEDC.Derived.FieldUp
