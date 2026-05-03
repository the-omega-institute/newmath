import BEDC.Derived.FieldUp.RatDenominatorUnitEnvelopeContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_denominator_unit_envelope_classifier_append_closed {h h' k k' : BHist} :
    ((RatHistoryCarrier h ∧ RatHistoryCarrier h' ∧ RatHistoryClassifier h h') ∨
        (hsame h BHist.Empty ∧ hsame h' BHist.Empty)) ->
      ((RatHistoryCarrier k ∧ RatHistoryCarrier k' ∧ RatHistoryClassifier k k') ∨
        (hsame k BHist.Empty ∧ hsame k' BHist.Empty)) ->
        ((RatHistoryCarrier (append h k) ∧ RatHistoryCarrier (append h' k') ∧
            RatHistoryClassifier (append h k) (append h' k')) ∨
          (hsame (append h k) BHist.Empty ∧ hsame (append h' k') BHist.Empty)) := by
  intro left right
  cases left with
  | inl leftCarried =>
      cases right with
      | inl rightCarried =>
          apply Or.inl
          have rightClassifier : RatHistoryClassifier k k' := rightCarried.right.right
          have tailSame : hsame k k' := rightClassifier.right.right
          have tailUnary : UnaryHistory k :=
            (PositiveUnaryDenominator_unary_and_nonempty
              (RatHistoryCarrier_iff_positive_denominator.mp rightCarried.left)).left
          have appendedClassifier :
              RatHistoryClassifier (append h k) (append h' k') :=
            RatHistoryClassifier_append_unary_denominator_closed leftCarried.right.right
              tailUnary tailSame
          exact And.intro appendedClassifier.left
            (And.intro appendedClassifier.right.left appendedClassifier)
      | inr rightEmpty =>
          apply Or.inl
          cases rightEmpty.left
          cases rightEmpty.right
          have appendedClassifier :
              RatHistoryClassifier (append h BHist.Empty) (append h' BHist.Empty) :=
            RatHistoryClassifier_hsame_transport
              (hsame_symm (append_empty_right h)) (hsame_symm (append_empty_right h'))
              leftCarried.right.right
          exact And.intro appendedClassifier.left
            (And.intro appendedClassifier.right.left appendedClassifier)
  | inr leftEmpty =>
      cases right with
      | inl rightCarried =>
          apply Or.inl
          cases leftEmpty.left
          cases leftEmpty.right
          have appendedClassifier :
              RatHistoryClassifier (append BHist.Empty k) (append BHist.Empty k') :=
            RatHistoryClassifier_hsame_transport
              (hsame_symm (append_empty_left k)) (hsame_symm (append_empty_left k'))
              rightCarried.right.right
          exact And.intro appendedClassifier.left
            (And.intro appendedClassifier.right.left appendedClassifier)
      | inr rightEmpty =>
          apply Or.inr
          cases leftEmpty.left
          cases leftEmpty.right
          cases rightEmpty.left
          cases rightEmpty.right
          exact And.intro rfl rfl

theorem field_rat_denominator_unit_envelope_classifier_exactness {h k : BHist} :
    (RatHistoryCarrier h -> RatHistoryCarrier k ->
      (FieldRatDenominatorUnitEnvelopeClassifier h k <-> RatHistoryClassifier h k)) ∧
    (RatHistoryCarrier h -> hsame k BHist.Empty ->
      FieldRatDenominatorUnitEnvelopeClassifier h k -> False) ∧
    (hsame h BHist.Empty -> RatHistoryCarrier k ->
      FieldRatDenominatorUnitEnvelopeClassifier h k -> False) ∧
    (hsame h BHist.Empty -> hsame k BHist.Empty ->
      FieldRatDenominatorUnitEnvelopeClassifier h k) := by
  constructor
  · intro carrierH carrierK
    constructor
    · intro classified
      cases classified with
      | inl ratData =>
          exact ratData.right.right
      | inr emptyData =>
          exact False.elim (RatHistoryCarrier_not_empty carrierH emptyData.left)
    · intro ratClassified
      exact Or.inl ⟨carrierH, carrierK, ratClassified⟩
  constructor
  · intro carrierH emptyK classified
    cases classified with
    | inl ratData =>
        exact RatHistoryCarrier_not_empty ratData.right.left emptyK
    | inr emptyData =>
        exact RatHistoryCarrier_not_empty carrierH emptyData.left
  constructor
  · intro emptyH carrierK classified
    cases classified with
    | inl ratData =>
        exact RatHistoryCarrier_not_empty ratData.left emptyH
    | inr emptyData =>
        exact RatHistoryCarrier_not_empty carrierK emptyData.right
  · intro emptyH emptyK
    exact Or.inr ⟨emptyH, emptyK⟩

theorem field_rat_denominator_unit_envelope_unit_unique {u : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier u ->
      ((∀ {h : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeClassifier (append h u) h) ->
          FieldRatDenominatorUnitEnvelopeClassifier u BHist.Empty) ∧
      ((∀ {h : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeClassifier (append u h) h) ->
          FieldRatDenominatorUnitEnvelopeClassifier u BHist.Empty) := by
  intro carrierU
  constructor
  · intro rightUnitLaw
    cases carrierU with
    | inl ratU =>
        have ratRightUnit :
            ∀ {d r : BHist}, RatHistoryCarrier d -> Cont d u r -> RatHistoryClassifier r d := by
          intro d r carrierD continuation
          have envelopeResult :
              FieldRatDenominatorUnitEnvelopeClassifier (append d u) d :=
            rightUnitLaw (Or.inl carrierD)
          have carrierDU : RatHistoryCarrier (append d u) :=
            RatHistoryCarrier_continuation_closed carrierD ratU (cont_intro rfl)
          have ratResult : RatHistoryClassifier (append d u) d :=
            Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left carrierDU
              carrierD) envelopeResult
          cases continuation
          exact ratResult
        exact Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff
          (field_rat_denominator_continuation_unit_endpoint_empty.left ratRightUnit)
    | inr emptyU =>
        exact Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff emptyU
  · intro leftUnitLaw
    cases carrierU with
    | inl ratU =>
        have ratLeftUnit :
            ∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d := by
          intro d r carrierD continuation
          have envelopeResult :
              FieldRatDenominatorUnitEnvelopeClassifier (append u d) d :=
            leftUnitLaw (Or.inl carrierD)
          have carrierUD : RatHistoryCarrier (append u d) :=
            RatHistoryCarrier_continuation_closed ratU carrierD (cont_intro rfl)
          have ratResult : RatHistoryClassifier (append u d) d :=
            Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left carrierUD
              carrierD) envelopeResult
          cases continuation
          exact ratResult
        exact Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff
          (field_rat_denominator_continuation_unit_endpoint_empty.right.left ratLeftUnit)
    | inr emptyU =>
        exact Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff emptyU

theorem field_rat_denominator_unit_envelope_unit_iff {u : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier u ->
      (FieldRatDenominatorUnitEnvelopeClassifier u BHist.Empty ↔
        ((∀ {h : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
          FieldRatDenominatorUnitEnvelopeClassifier (append h u) h) ∧
         (∀ {h : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
          FieldRatDenominatorUnitEnvelopeClassifier (append u h) h))) := by
  intro carrierU
  constructor
  · intro classifiedU
    have emptyU : hsame u BHist.Empty :=
      Iff.mp FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff classifiedU
    constructor
    · intro h carrierH
      cases emptyU
      exact field_rat_denominator_unit_envelope_monoid_laws.right.right.right.left carrierH |>.right
    · intro h carrierH
      cases emptyU
      exact field_rat_denominator_unit_envelope_monoid_laws.right.right.right.left carrierH |>.left
  · intro unitLaws
    exact (field_rat_denominator_unit_envelope_unit_unique carrierU).left unitLaws.left

theorem field_rat_denominator_unit_envelope_strict_support_laws {h k : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier k ->
      (FieldRatDenominatorUnitEnvelopeClassifier h k ->
        (RatHistoryCarrier h <-> RatHistoryCarrier k)) ∧
      (RatHistoryCarrier (append h k) <-> RatHistoryCarrier h ∨ RatHistoryCarrier k) := by
  intro carrierH carrierK
  constructor
  · intro classified
    cases classified with
    | inl ratData =>
        constructor
        · intro _ratH
          exact ratData.right.left
        · intro _ratK
          exact ratData.left
    | inr emptyData =>
        constructor
        · intro ratH
          exact False.elim (RatHistoryCarrier_not_empty ratH emptyData.left)
        · intro ratK
          exact False.elim (RatHistoryCarrier_not_empty ratK emptyData.right)
  · constructor
    · intro appendCarrier
      cases carrierH with
      | inl ratH =>
          exact Or.inl ratH
      | inr emptyH =>
          cases carrierK with
          | inl ratK =>
              exact Or.inr ratK
          | inr emptyK =>
              cases emptyH
              cases emptyK
              exact False.elim (RatHistoryCarrier_not_empty appendCarrier rfl)
    · intro factorCarrier
      cases factorCarrier with
      | inl ratH =>
          cases carrierK with
          | inl ratK =>
              exact RatHistoryCarrier_continuation_closed ratH ratK (cont_intro rfl)
          | inr emptyK =>
              cases emptyK
              exact ratH
      | inr ratK =>
          cases carrierH with
          | inl ratH =>
              exact RatHistoryCarrier_continuation_closed ratH ratK (cont_intro rfl)
          | inr emptyH =>
              cases emptyH
              exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left k)) ratK

theorem field_rat_denominator_unit_envelope_empty_product_reflection {h k : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier k ->
      (FieldRatDenominatorUnitEnvelopeClassifier (append h k) BHist.Empty <->
        FieldRatDenominatorUnitEnvelopeClassifier h BHist.Empty ∧
          FieldRatDenominatorUnitEnvelopeClassifier k BHist.Empty) := by
  intro _carrierH _carrierK
  constructor
  · intro classifiedProduct
    have productEmpty : hsame (append h k) BHist.Empty :=
      Iff.mp FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff classifiedProduct
    have splitEmpty : h = BHist.Empty ∧ k = BHist.Empty :=
      append_eq_empty_iff.mp productEmpty
    exact And.intro
      (Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff splitEmpty.left)
      (Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff splitEmpty.right)
  · intro classifiedFactors
    have emptyH : hsame h BHist.Empty :=
      Iff.mp FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff classifiedFactors.left
    have emptyK : hsame k BHist.Empty :=
      Iff.mp FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff classifiedFactors.right
    have productEmpty : hsame (append h k) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro emptyH emptyK)
    exact Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff productEmpty

theorem field_rat_denominator_unit_envelope_support_unit_no_confusion {h k : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier k ->
      (RatHistoryCarrier h <->
        (FieldRatDenominatorUnitEnvelopeClassifier h BHist.Empty -> False)) ∧
      ((FieldRatDenominatorUnitEnvelopeClassifier (append h k) BHist.Empty -> False) <->
        RatHistoryCarrier h ∨ RatHistoryCarrier k) := by
  intro carrierH carrierK
  have noConfusion :
      ∀ {t : BHist}, FieldRatDenominatorUnitEnvelopeCarrier t ->
        (RatHistoryCarrier t <->
          (FieldRatDenominatorUnitEnvelopeClassifier t BHist.Empty -> False)) := by
    intro t carrierT
    constructor
    · intro ratT classifiedUnit
      exact RatHistoryCarrier_not_empty ratT
        (Iff.mp FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff classifiedUnit)
    · intro rejectsUnit
      cases carrierT with
      | inl ratT =>
          exact ratT
      | inr emptyT =>
          exact False.elim
            (rejectsUnit
              (Iff.mpr FieldRatDenominatorUnitEnvelopeClassifier_empty_right_iff emptyT))
  have productCarrier :
      FieldRatDenominatorUnitEnvelopeCarrier (append h k) :=
    field_rat_denominator_unit_envelope_monoid_laws.right.left carrierH carrierK
  have productNoConfusion := noConfusion productCarrier
  have productSupport :=
    (field_rat_denominator_unit_envelope_strict_support_laws carrierH carrierK).right
  constructor
  · exact noConfusion carrierH
  · constructor
    · intro rejectsProductUnit
      exact Iff.mp productSupport (Iff.mpr productNoConfusion rejectsProductUnit)
    · intro factorSupport
      exact Iff.mp productNoConfusion (Iff.mpr productSupport factorSupport)

theorem FieldRatDenominatorUnitEnvelopeClassifier_empty_context_iff {p q p' q' h k : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty ->
        (FieldRatDenominatorUnitEnvelopeClassifier (append p (append h q))
          (append p' (append k q')) <-> FieldRatDenominatorUnitEnvelopeClassifier h k) := by
  intro sameP sameQ sameP' sameQ'
  have leftSame : hsame (append p (append h q)) h := by
    cases sameP
    cases sameQ
    exact hsame_trans (append_empty_left (append h BHist.Empty)) (append_empty_right h)
  have rightSame : hsame (append p' (append k q')) k := by
    cases sameP'
    cases sameQ'
    exact hsame_trans (append_empty_left (append k BHist.Empty)) (append_empty_right k)
  constructor
  · intro classified
    cases classified with
    | inl ratData =>
        have classifiedCore : RatHistoryClassifier h k :=
          RatHistoryClassifier_hsame_transport leftSame rightSame ratData.right.right
        exact Or.inl ⟨classifiedCore.left, classifiedCore.right.left, classifiedCore⟩
    | inr emptyData =>
        exact Or.inr
          ⟨hsame_trans (hsame_symm leftSame) emptyData.left,
            hsame_trans (hsame_symm rightSame) emptyData.right⟩
  · intro classified
    cases classified with
    | inl ratData =>
        have classifiedContext :
            RatHistoryClassifier (append p (append h q)) (append p' (append k q')) :=
          RatHistoryClassifier_hsame_transport (hsame_symm leftSame) (hsame_symm rightSame)
            ratData.right.right
        exact Or.inl
          ⟨classifiedContext.left, classifiedContext.right.left, classifiedContext⟩
    | inr emptyData =>
        exact Or.inr
          ⟨hsame_trans leftSame emptyData.left, hsame_trans rightSame emptyData.right⟩

theorem field_rat_denominator_bilateral_strict_factor_cancellation {h k l r : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier k ->
      RatHistoryCarrier l -> RatHistoryCarrier r ->
        (FieldRatDenominatorUnitEnvelopeClassifier (append l (append h r))
          (append l (append k r)) <-> FieldRatDenominatorUnitEnvelopeClassifier h k) := by
  intro carrierH carrierK ratL ratR
  have unaryL : UnaryHistory l :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp ratL)).left
  have unaryR : UnaryHistory r :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp ratR)).left
  have contextCarrier :
      ∀ {x : BHist}, FieldRatDenominatorUnitEnvelopeCarrier x ->
        RatHistoryCarrier (append l (append x r)) := by
    intro x carrierX
    cases carrierX with
    | inl ratX =>
        have carrierXR : RatHistoryCarrier (append x r) :=
          RatHistoryCarrier_continuation_closed ratX ratR (cont_intro rfl)
        exact RatHistoryCarrier_continuation_closed ratL carrierXR (cont_intro rfl)
    | inr emptyX =>
        cases emptyX
        have carrierLR : RatHistoryCarrier (append l r) :=
          RatHistoryCarrier_continuation_closed ratL ratR (cont_intro rfl)
        exact RatHistoryCarrier_hsame_transport
          (hsame_symm (congrArg (append l) (append_empty_left r))) carrierLR
  have contextClassifierIff :
      ∀ {a b : BHist}, RatHistoryCarrier a -> RatHistoryCarrier b ->
        (RatHistoryClassifier a b <->
          RatHistoryClassifier (append l (append a r)) (append l (append b r))) := by
    intro a b ratA ratB
    exact field_rat_denominator_continuation_common_context_classifier_exactness unaryL unaryR
      ratA ratB (cont_intro rfl) (cont_intro rfl) (cont_intro (append_assoc l a r).symm)
      (cont_intro (append_assoc l b r).symm)
  have contextSameCancel :
      ∀ {a b : BHist},
        hsame (append l (append a r)) (append l (append b r)) -> hsame a b := by
    intro a b same
    exact cont_cancel_common_context (cont_intro rfl) (cont_intro (append_assoc l a r).symm)
      (cont_intro rfl) (cont_intro (append_assoc l b r).symm) same
  have carrierLeftContext : RatHistoryCarrier (append l (append h r)) :=
    contextCarrier carrierH
  have carrierRightContext : RatHistoryCarrier (append l (append k r)) :=
    contextCarrier carrierK
  constructor
  · intro classifiedContext
    cases carrierH with
    | inl ratH =>
        cases carrierK with
        | inl ratK =>
            have ratContext : RatHistoryClassifier (append l (append h r))
                (append l (append k r)) :=
              Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left
                carrierLeftContext carrierRightContext) classifiedContext
            have ratHK : RatHistoryClassifier h k :=
              Iff.mpr (contextClassifierIff ratH ratK) ratContext
            exact Or.inl ⟨ratHK.left, ratHK.right.left, ratHK⟩
        | inr emptyK =>
            cases emptyK
            have ratContext : RatHistoryClassifier (append l (append h r))
                (append l (append BHist.Empty r)) :=
              Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left
                carrierLeftContext carrierRightContext) classifiedContext
            have sameHEmpty : hsame h BHist.Empty :=
              contextSameCancel ratContext.right.right
            exact False.elim (RatHistoryCarrier_not_empty ratH sameHEmpty)
    | inr emptyH =>
        cases emptyH
        cases carrierK with
        | inl ratK =>
            have ratContext : RatHistoryClassifier (append l (append BHist.Empty r))
                (append l (append k r)) :=
              Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left
                carrierLeftContext carrierRightContext) classifiedContext
            have sameEmptyK : hsame BHist.Empty k :=
              contextSameCancel ratContext.right.right
            exact False.elim (RatHistoryCarrier_not_empty ratK (hsame_symm sameEmptyK))
        | inr emptyK =>
            cases emptyK
            exact Or.inr ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩
  · intro classified
    cases carrierH with
    | inl ratH =>
        cases carrierK with
        | inl ratK =>
            have ratHK : RatHistoryClassifier h k :=
              Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left ratH ratK)
                classified
            have ratContext : RatHistoryClassifier (append l (append h r))
                (append l (append k r)) :=
              Iff.mp (contextClassifierIff ratH ratK) ratHK
            exact Or.inl ⟨ratContext.left, ratContext.right.left, ratContext⟩
        | inr emptyK =>
            exact False.elim
              ((field_rat_denominator_unit_envelope_classifier_exactness.right.left ratH emptyK)
                classified)
    | inr emptyH =>
        cases carrierK with
        | inl ratK =>
            exact False.elim
              ((field_rat_denominator_unit_envelope_classifier_exactness.right.right.left emptyH
                ratK) classified)
        | inr emptyK =>
            cases emptyH
            cases emptyK
            exact Or.inl
              ⟨carrierLeftContext, carrierRightContext, carrierLeftContext, carrierRightContext,
                hsame_refl (append l (append BHist.Empty r))⟩

theorem field_rat_denominator_unit_envelope_cancellation_exactness {h k t : BHist} :
    FieldRatDenominatorUnitEnvelopeCarrier h -> FieldRatDenominatorUnitEnvelopeCarrier k ->
      FieldRatDenominatorUnitEnvelopeCarrier t -> RatHistoryCarrier t ->
        (FieldRatDenominatorUnitEnvelopeClassifier (append h t) (append k t) <->
            FieldRatDenominatorUnitEnvelopeClassifier h k) ∧
          (FieldRatDenominatorUnitEnvelopeClassifier (append t h) (append t k) <->
            FieldRatDenominatorUnitEnvelopeClassifier h k) := by
  intro carrierH carrierK _carrierT ratT
  have carrierAppendRight :
      ∀ {x : BHist}, FieldRatDenominatorUnitEnvelopeCarrier x ->
        RatHistoryCarrier (append x t) := by
    intro x carrierX
    cases carrierX with
    | inl ratX =>
        exact RatHistoryCarrier_continuation_closed ratX ratT (cont_intro rfl)
    | inr emptyX =>
        cases emptyX
        exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left t)) ratT
  have carrierAppendLeft :
      ∀ {x : BHist}, FieldRatDenominatorUnitEnvelopeCarrier x ->
        RatHistoryCarrier (append t x) := by
    intro x carrierX
    cases carrierX with
    | inl ratX =>
        exact RatHistoryCarrier_continuation_closed ratT ratX (cont_intro rfl)
    | inr emptyX =>
        cases emptyX
        exact ratT
  have ratTT : RatHistoryClassifier t t := ⟨ratT, ratT, hsame_refl t⟩
  constructor
  · constructor
    · intro classifiedContext
      have ratContext : RatHistoryClassifier (append h t) (append k t) :=
        Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left
          (carrierAppendRight carrierH) (carrierAppendRight carrierK)) classifiedContext
      cases carrierH with
      | inl ratH =>
          cases carrierK with
          | inl ratK =>
              have ratHK : RatHistoryClassifier h k :=
                ⟨ratH, ratK, append_right_cancel ratContext.right.right⟩
              exact Or.inl ⟨ratH, ratK, ratHK⟩
          | inr emptyK =>
              cases emptyK
              exact False.elim
                (RatHistoryCarrier_not_empty ratH (append_right_cancel ratContext.right.right))
      | inr emptyH =>
          cases carrierK with
          | inl ratK =>
              cases emptyH
              exact False.elim
                (RatHistoryCarrier_not_empty ratK
                  (hsame_symm (append_right_cancel ratContext.right.right)))
          | inr emptyK =>
              exact Or.inr ⟨emptyH, emptyK⟩
    · intro classified
      exact field_rat_denominator_unit_envelope_classifier_append_closed classified
        (Or.inl ⟨ratT, ratT, ratTT⟩)
  · constructor
    · intro classifiedContext
      have ratContext : RatHistoryClassifier (append t h) (append t k) :=
        Iff.mp (field_rat_denominator_unit_envelope_classifier_exactness.left
          (carrierAppendLeft carrierH) (carrierAppendLeft carrierK)) classifiedContext
      cases carrierH with
      | inl ratH =>
          cases carrierK with
          | inl ratK =>
              have ratHK : RatHistoryClassifier h k :=
                ⟨ratH, ratK, append_left_cancel ratContext.right.right⟩
              exact Or.inl ⟨ratH, ratK, ratHK⟩
          | inr emptyK =>
              cases emptyK
              exact False.elim
                (RatHistoryCarrier_not_empty ratH (append_left_cancel ratContext.right.right))
      | inr emptyH =>
          cases carrierK with
          | inl ratK =>
              cases emptyH
              exact False.elim
                (RatHistoryCarrier_not_empty ratK
                  (hsame_symm (append_left_cancel ratContext.right.right)))
          | inr emptyK =>
              exact Or.inr ⟨emptyH, emptyK⟩
    · intro classified
      exact field_rat_denominator_unit_envelope_classifier_append_closed
        (Or.inl ⟨ratT, ratT, ratTT⟩) classified

theorem FieldRatDenominatorUnitEnvelope_external_strict :
    FieldRatDenominatorUnitEnvelopeCarrier BHist.Empty ∧
      (RatHistoryCarrier BHist.Empty -> False) ∧
      (∀ {h : BHist}, RatHistoryCarrier h ->
        FieldRatDenominatorUnitEnvelopeClassifier h BHist.Empty -> False) ∧
      (∀ {h : BHist}, RatHistoryCarrier h ->
        FieldRatDenominatorUnitEnvelopeClassifier BHist.Empty h -> False) ∧
      (∀ {h k : BHist}, RatHistoryCarrier h -> RatHistoryCarrier k ->
        (FieldRatDenominatorUnitEnvelopeClassifier h k <-> RatHistoryClassifier h k)) := by
  constructor
  · exact field_rat_denominator_unit_envelope_monoid_laws.left
  constructor
  · intro emptyCarrier
    exact RatHistoryCarrier_not_empty emptyCarrier (hsame_refl BHist.Empty)
  constructor
  · intro h ratH classified
    exact (field_rat_denominator_unit_envelope_classifier_exactness.right.left ratH
      (hsame_refl BHist.Empty)) classified
  constructor
  · intro h ratH classified
    exact (field_rat_denominator_unit_envelope_classifier_exactness.right.right.left
      (hsame_refl BHist.Empty) ratH) classified
  · intro h k ratH ratK
    exact field_rat_denominator_unit_envelope_classifier_exactness.left ratH ratK

theorem field_rat_denominator_unit_envelope_commutative_monoid_laws :
    (FieldRatDenominatorUnitEnvelopeCarrier BHist.Empty ∧
      (∀ {h k : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeCarrier k ->
          FieldRatDenominatorUnitEnvelopeCarrier (append h k)) ∧
      (∀ {h k l : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeCarrier k -> FieldRatDenominatorUnitEnvelopeCarrier l ->
          FieldRatDenominatorUnitEnvelopeClassifier (append (append h k) l)
            (append h (append k l))) ∧
      (∀ {h : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeClassifier (append BHist.Empty h) h ∧
          FieldRatDenominatorUnitEnvelopeClassifier (append h BHist.Empty) h) ∧
      (∀ {h h' k k' : BHist}, FieldRatDenominatorUnitEnvelopeClassifier h h' ->
        FieldRatDenominatorUnitEnvelopeClassifier k k' ->
          FieldRatDenominatorUnitEnvelopeClassifier (append h k) (append h' k'))) ∧
      (∀ {h k : BHist}, FieldRatDenominatorUnitEnvelopeCarrier h ->
        FieldRatDenominatorUnitEnvelopeCarrier k ->
          FieldRatDenominatorUnitEnvelopeClassifier (append h k) (append k h)) := by
  constructor
  · exact field_rat_denominator_unit_envelope_monoid_laws
  · intro h k carrierH carrierK
    cases carrierH with
    | inl ratH =>
        cases carrierK with
        | inl ratK =>
            have classified :
                RatHistoryClassifier (append h k) (append k h) :=
              field_rat_denominator_continuation_commutative_classifier ratH ratK
                (cont_intro rfl) (cont_intro rfl)
            exact Or.inl ⟨classified.left, classified.right.left, classified⟩
        | inr emptyK =>
            cases emptyK
            have classified :
                RatHistoryClassifier (append h BHist.Empty) (append BHist.Empty h) :=
              RatHistoryClassifier_hsame_transport (append_empty_right h).symm
                (append_empty_left h).symm ⟨ratH, ratH, hsame_refl h⟩
            exact Or.inl ⟨classified.left, classified.right.left, classified⟩
    | inr emptyH =>
        cases carrierK with
        | inl ratK =>
            cases emptyH
            have classified :
                RatHistoryClassifier (append BHist.Empty k) (append k BHist.Empty) :=
              RatHistoryClassifier_hsame_transport (append_empty_left k).symm
                (append_empty_right k).symm ⟨ratK, ratK, hsame_refl k⟩
            exact Or.inl ⟨classified.left, classified.right.left, classified⟩
        | inr emptyK =>
            cases emptyH
            cases emptyK
            exact Or.inr ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩
end BEDC.Derived.FieldUp
