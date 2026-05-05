import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont.Units
import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_vector_space_over_base :
    SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier ∧
      (forall {r m : BHist}, FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
          FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
            FieldSingletonClassifier (VecSpaceSingletonSmul r m) (FieldSingletonMul r m)) := by
  constructor
  · exact VecSpaceSingleton_semanticNameCert
  · intro r m _carrierR _carrierM
    have vecActionEmpty :
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty :=
      And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    have fieldMulEmpty :
        FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty :=
      And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    have actionMulCompatible :
        FieldSingletonClassifier (VecSpaceSingletonSmul r m) (FieldSingletonMul r m) :=
      And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    exact And.intro vecActionEmpty (And.intro fieldMulEmpty actionMulCompatible)

theorem FieldExtSingleton_certificate_obligation_package :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier ∧
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier ∧
      NameCert FieldSingletonCarrier FieldSingletonClassifier ∧
      NameCert VecSpaceSingletonCarrier VecSpaceSingletonClassifier ∧
      (forall {h : BHist}, FieldSingletonCarrier h -> Cont BHist.Empty h h) := by
  have fieldCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier :=
    singleton_empty_history_field_schema_laws.left
  have vecCert :
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier :=
    VecSpaceSingleton_semanticNameCert
  exact And.intro fieldCert
    (And.intro vecCert
      (And.intro fieldCert.core
        (And.intro vecCert.core
          (by
            intro h _carrierH
            exact cont_intro (append_empty_left h).symm))))

theorem FieldExtSingleton_identity_tower_continuation_classified {h middle top : BHist} :
    FieldSingletonCarrier h -> Cont h BHist.Empty middle -> Cont middle BHist.Empty top ->
      FieldSingletonClassifier top h ∧ hsame middle top := by
  intro carrierH first second
  have sameMiddleH : hsame middle h := cont_right_unit_result first
  have sameTopMiddle : hsame top middle := cont_right_unit_result second
  have carrierMiddle : FieldSingletonCarrier middle := hsame_trans sameMiddleH carrierH
  have carrierTop : FieldSingletonCarrier top := hsame_trans sameTopMiddle carrierMiddle
  have sameTopH : hsame top h := hsame_trans sameTopMiddle sameMiddleH
  exact And.intro
    (And.intro carrierTop (And.intro carrierH sameTopH))
    (hsame_symm sameTopMiddle)

theorem FieldExtSingleton_scalar_action_mul_endpoint_classified {r m : BHist} :
    FieldSingletonCarrier r -> FieldSingletonCarrier m ->
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) (FieldSingletonMul r m) ∧
        FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty := by
  intro _carrierR _carrierM
  have emptyCarrier : hsame BHist.Empty BHist.Empty := hsame_refl BHist.Empty
  exact And.intro
    (And.intro emptyCarrier (And.intro emptyCarrier emptyCarrier))
    (And.intro emptyCarrier (And.intro emptyCarrier emptyCarrier))

theorem FieldExtSingleton_semantic_name_certificate :
    SemanticNameCert FieldSingletonCarrier
      (fun h : BHist => FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h)
      (fun h : BHist => FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h)
      FieldSingletonClassifier := by
  have fieldCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier :=
    singleton_empty_history_field_schema_laws.left
  exact {
    core := fieldCert.core
    pattern_sound := by
      intro _h source
      exact And.intro source source
    ledger_sound := by
      intro _h source
      exact And.intro source source
  }

theorem FieldExtSingleton_vector_action_field_mul_context_readback {L R r m out : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier (append L (VecSpaceSingletonSmul r m)) (append R out) ->
        FieldSingletonClassifier (append L (FieldSingletonMul r m)) (append R out) ∧
          hsame out BHist.Empty := by
  intro _carrierL _carrierR _carrierM classified
  have rightEmpty : append R out = BHist.Empty := classified.right.left
  have outEmpty : hsame out BHist.Empty := (append_eq_empty_iff.mp rightEmpty).right
  exact And.intro classified outEmpty

def FieldExtSingletonCarrier (h : BHist) : Prop :=
  FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h

def FieldExtSingletonClassifier (h k : BHist) : Prop :=
  FieldSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k

theorem FieldExtSingleton_embedding_obligations :
    SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier ∧
      (forall {h k : BHist}, FieldExtSingletonClassifier h k ->
        FieldSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k) ∧
      (forall {h k : BHist}, FieldSingletonClassifier h k -> VecSpaceSingletonClassifier h k ->
        FieldExtSingletonClassifier h k) := by
  have emptyCarrier : FieldExtSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have semantic :
      SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro
          (And.intro carrier.left (And.intro carrier.left (hsame_refl h)))
          (And.intro carrier.right (And.intro carrier.right (hsame_refl h)))
      equiv_symm := by
        intro h k same
        exact And.intro
          (And.intro same.left.right.left
            (And.intro same.left.left (hsame_symm same.left.right.right)))
          (And.intro same.right.right.left
            (And.intro same.right.left (hsame_symm same.right.right.right)))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro
          (And.intro sameHK.left.left
            (And.intro sameKR.left.right.left
              (hsame_trans sameHK.left.right.right sameKR.left.right.right)))
          (And.intro sameHK.right.left
            (And.intro sameKR.right.right.left
              (hsame_trans sameHK.right.right.right sameKR.right.right.right)))
      carrier_respects_equiv := by
        intro _h _k same _carrier
        exact And.intro same.left.right.left same.right.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }
  exact And.intro semantic
    (And.intro
      (by
        intro h k classified
        exact classified)
      (by
        intro h k fieldClassified vecClassified
        exact And.intro fieldClassified vecClassified))

def FieldExtSingletonEmbedding (h : BHist) : BHist :=
  append BHist.Empty h

def FieldExtSingletonLedgerPolicy (h : BHist) : Prop :=
  FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
    FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h)

theorem FieldExtSingletonLedgerPolicy_carrier_coincidence {h : BHist} :
    FieldExtSingletonLedgerPolicy h ->
      FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
        FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h) := by
  intro policy
  cases policy with
  | intro fieldCarrier rest =>
      cases rest with
      | intro vecCarrier embeddedClassifier =>
          exact And.intro fieldCarrier (And.intro vecCarrier embeddedClassifier)

theorem FieldExtSingletonVectorSpace_smul_mul_compatible {r m : BHist} :
    FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      VecSpaceSingletonCarrier (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m) ∧
        FieldSingletonCarrier (FieldSingletonMul (FieldExtSingletonEmbedding r) m) ∧
          hsame (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m)
            (FieldSingletonMul (FieldExtSingletonEmbedding r) m) := by
  intro _carrierR _carrierM
  have smulCarrier :
      VecSpaceSingletonCarrier (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m) :=
    hsame_refl BHist.Empty
  have mulCarrier :
      FieldSingletonCarrier (FieldSingletonMul (FieldExtSingletonEmbedding r) m) :=
    hsame_refl BHist.Empty
  exact And.intro smulCarrier
    (And.intro mulCarrier (hsame_refl BHist.Empty))

theorem FieldExtSingletonEmbedding_laws :
    FieldSingletonCarrier BHist.Empty ∧
      (forall {h : BHist}, FieldSingletonCarrier h ->
        FieldSingletonCarrier (FieldExtSingletonEmbedding h)) ∧
      (forall {h k : BHist}, FieldSingletonClassifier h k <->
        FieldSingletonClassifier (FieldExtSingletonEmbedding h)
          (FieldExtSingletonEmbedding k)) ∧
      FieldSingletonClassifier (FieldExtSingletonEmbedding FieldSingletonZero)
        FieldSingletonZero ∧
      FieldSingletonClassifier (FieldExtSingletonEmbedding FieldSingletonOne)
        FieldSingletonOne := by
  have emptyCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · exact emptyCarrier
  · constructor
    · intro h carrierH
      unfold FieldExtSingletonEmbedding
      exact hsame_trans (append_empty_left h) carrierH
    · constructor
      · intro h k
        constructor
        · intro classified
          have embeddedH : FieldSingletonCarrier (FieldExtSingletonEmbedding h) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left h) classified.left
          have embeddedK : FieldSingletonCarrier (FieldExtSingletonEmbedding k) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left k) classified.right.left
          have embeddedSame :
              hsame (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left h)
              (hsame_trans classified.right.right (hsame_symm (append_empty_left k)))
          exact And.intro embeddedH (And.intro embeddedK embeddedSame)
        · intro classified
          have carrierH : FieldSingletonCarrier h := by
            unfold FieldExtSingletonEmbedding at classified
            exact hsame_trans (hsame_symm (append_empty_left h)) classified.left
          have carrierK : FieldSingletonCarrier k := by
            unfold FieldExtSingletonEmbedding at classified
            exact hsame_trans (hsame_symm (append_empty_left k)) classified.right.left
          have sameHK : hsame h k := by
            unfold FieldExtSingletonEmbedding at classified
            exact hsame_trans (hsame_symm (append_empty_left h))
              (hsame_trans classified.right.right (append_empty_left k))
          exact And.intro carrierH (And.intro carrierK sameHK)
      · constructor
        · unfold FieldExtSingletonEmbedding FieldSingletonZero FieldSingletonClassifier
          exact And.intro emptyCarrier
            (And.intro emptyCarrier (hsame_refl BHist.Empty))
        · unfold FieldExtSingletonEmbedding FieldSingletonOne FieldSingletonClassifier
          exact And.intro emptyCarrier
            (And.intro emptyCarrier (hsame_refl BHist.Empty))

theorem FieldExtRatReflexiveEmbedding_denominator_package {h k : BHist} :
    RatHistoryClassifier h k ->
      PositiveUnaryDenominator (FieldExtSingletonEmbedding h) ∧
        PositiveUnaryDenominator (FieldExtSingletonEmbedding k) ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
            (hsame (FieldExtSingletonEmbedding h) BHist.Empty -> False) ∧
              (hsame (FieldExtSingletonEmbedding k) BHist.Empty -> False) := by
  intro classified
  have embeddedClassifier :
      RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryClassifier_hsame_transport
      (hsame_symm (append_empty_left h)) (hsame_symm (append_empty_left k)) classified
  have positives :
      PositiveUnaryDenominator (FieldExtSingletonEmbedding h) ∧
        PositiveUnaryDenominator (FieldExtSingletonEmbedding k) :=
    RatHistoryClassifier_positive_denominators embeddedClassifier
  have nonempty :
      (hsame (FieldExtSingletonEmbedding h) BHist.Empty -> False) ∧
        (hsame (FieldExtSingletonEmbedding k) BHist.Empty -> False) :=
    RatHistoryClassifier_endpoints_not_empty embeddedClassifier
  exact And.intro positives.left
    (And.intro positives.right
      (And.intro embeddedClassifier
        (And.intro nonempty.left nonempty.right)))

theorem FieldExtRatReflexive_exact_endpoint_classification {h k : BHist} :
    RatHistoryClassifier h k ->
      RatHistoryClassifier (FieldExtSingletonEmbedding h) h ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding k) k ∧
          RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
  intro classified
  have carrierH : RatHistoryCarrier h := classified.left
  have carrierK : RatHistoryCarrier k := classified.right.left
  have embeddedH :
      RatHistoryClassifier (FieldExtSingletonEmbedding h) h := by
    unfold FieldExtSingletonEmbedding
    exact And.intro
      (RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left h)) carrierH)
      (And.intro carrierH (append_empty_left h))
  have embeddedK :
      RatHistoryClassifier (FieldExtSingletonEmbedding k) k := by
    unfold FieldExtSingletonEmbedding
    exact And.intro
      (RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left k)) carrierK)
      (And.intro carrierK (append_empty_left k))
  have embeddedHK :
      RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryClassifier_hsame_transport
      (hsame_symm (append_empty_left h)) (hsame_symm (append_empty_left k)) classified
  exact And.intro embeddedH (And.intro embeddedK embeddedHK)

theorem FieldExtSingletonEmbedding_identity_tower_package {h : BHist} :
    FieldSingletonCarrier h ->
      FieldSingletonClassifier (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h))
          (FieldExtSingletonEmbedding h) ∧
        Cont BHist.Empty (FieldExtSingletonEmbedding h)
          (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h)) ∧
          hsame (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h)) h := by
  intro carrierH
  have embeddedCarrier : FieldSingletonCarrier (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact hsame_trans (append_empty_left h) carrierH
  have doubleCarrier :
      FieldSingletonCarrier (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h)) := by
    unfold FieldExtSingletonEmbedding
    exact hsame_trans (append_empty_left (FieldExtSingletonEmbedding h)) embeddedCarrier
  have doubleSameEmbedded :
      hsame (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h))
        (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact append_empty_left (FieldExtSingletonEmbedding h)
  have towerCont :
      Cont BHist.Empty (FieldExtSingletonEmbedding h)
        (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h)) := by
    unfold FieldExtSingletonEmbedding
    exact cont_intro rfl
  have doubleSameH :
      hsame (FieldExtSingletonEmbedding (FieldExtSingletonEmbedding h)) h :=
    hsame_trans doubleSameEmbedded (hsame_trans (append_empty_left h) (hsame_refl h))
  exact And.intro
    (And.intro doubleCarrier (And.intro embeddedCarrier doubleSameEmbedded))
    (And.intro towerCont doubleSameH)

theorem FieldExtSingletonCarrier_coincidence {h : BHist} :
    FieldSingletonCarrier h ->
      FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
        FieldSingletonClassifier h BHist.Empty ∧
          VecSpaceSingletonClassifier h BHist.Empty := by
  intro carrier
  have emptyFieldCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have vecCarrier : VecSpaceSingletonCarrier h := carrier
  have fieldRow : FieldSingletonClassifier h BHist.Empty :=
    And.intro carrier (And.intro emptyFieldCarrier carrier)
  have vecRow : VecSpaceSingletonClassifier h BHist.Empty :=
    And.intro vecCarrier (And.intro emptyVecCarrier carrier)
  exact And.intro carrier (And.intro vecCarrier (And.intro fieldRow vecRow))

theorem FieldExtSingletonOperation_readback_exactness {r m : BHist} :
    FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier FieldSingletonZero BHist.Empty ∧
        FieldSingletonClassifier FieldSingletonOne BHist.Empty ∧
          FieldSingletonClassifier (FieldSingletonAdd r m) BHist.Empty ∧
            FieldSingletonClassifier (FieldSingletonNeg r) BHist.Empty ∧
              FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
                VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
                  FieldSingletonClassifier (FieldSingletonMul r m)
                    (VecSpaceSingletonSmul r m) := by
  intro _carrierR _carrierM
  have emptyFieldCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have fieldEmptyRow : FieldSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyFieldCarrier
      (And.intro emptyFieldCarrier (hsame_refl BHist.Empty))
  have vecEmptyRow : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyVecCarrier
      (And.intro emptyVecCarrier (hsame_refl BHist.Empty))
  exact And.intro fieldEmptyRow
    (And.intro fieldEmptyRow
      (And.intro fieldEmptyRow
        (And.intro fieldEmptyRow
          (And.intro fieldEmptyRow
            (And.intro vecEmptyRow fieldEmptyRow)))))

end BEDC.Derived.FieldExtUp
