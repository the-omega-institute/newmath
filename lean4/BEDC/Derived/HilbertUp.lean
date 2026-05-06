import BEDC.Derived.NormUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.Derived.MetricUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.NormUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.Derived.MetricUp
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def HilbertSingletonInnerProduct (_m _n : BHist) : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem HilbertSingleton_inner_product_norm_compatibility {m : BHist} :
    VecSpaceSingletonCarrier m ->
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m) (NormSingletonNorm m) ∧
        (RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
          (BHist.e1 (BHist.e1 BHist.Empty)) ↔ VecSpaceSingletonClassifier m BHist.Empty) := by
  intro carrierM
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m) (NormSingletonNorm m) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro realClassifier (NormSingletonEmptyHistory_zero_exactness carrierM)

theorem HilbertSingletonProjection_carried_endpoint {h : BHist} :
    VecSpaceSingletonCarrier h ->
      VecSpaceSingletonCarrier BHist.Empty ∧ VecSpaceSingletonClassifier h BHist.Empty ∧
        RealConstantHistoryClassifier (NormSingletonNorm BHist.Empty)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          RealConstantHistoryClassifier (HilbertSingletonInnerProduct h BHist.Empty)
            (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierH
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have endpointClassified : VecSpaceSingletonClassifier h BHist.Empty :=
    And.intro carrierH (And.intro emptyCarrier carrierH)
  have normClassified :
      RealConstantHistoryClassifier (NormSingletonNorm BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    (NormSingletonEmptyHistory_zero_exactness emptyCarrier).mpr emptyClassified
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have innerClassified :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct h BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold HilbertSingletonInnerProduct
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro emptyCarrier
    (And.intro endpointClassified (And.intro normClassified innerClassified))

theorem HilbertSingleton_constant_inner_product_transport {m m' n n' : BHist} :
    VecSpaceSingletonClassifier m m' -> VecSpaceSingletonClassifier n n' ->
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct m' n')
            (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
            (HilbertSingletonInnerProduct m' n') ∧
            RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
              (HilbertSingletonInnerProduct m' m') := by
  intro _classifiedM _classifiedN
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  have leftConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  have rightConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m' n')
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  have transported :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
        (HilbertSingletonInnerProduct m' n') := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  have normTransport :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
        (HilbertSingletonInnerProduct m' m') := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  exact And.intro leftConstant
    (And.intro rightConstant
      (And.intro transported normTransport))

theorem HilbertSingleton_classifier_source_boundary {m n : BHist} :
    VecSpaceSingletonClassifier m n ->
      VecSpaceSingletonCarrier m ∧
        VecSpaceSingletonCarrier n ∧
          hsame m BHist.Empty ∧
            hsame n BHist.Empty ∧
              RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
                (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro classified
  cases classified with
  | intro carrierM rest =>
      cases rest with
      | intro carrierN _sameMN =>
          have sameMEmpty : hsame m BHist.Empty := carrierM
          have sameNEmpty : hsame n BHist.Empty := carrierN
          have emptyUnary : UnaryHistory BHist.Empty := unary_empty
          have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
            RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
          have ratClassifier :
              RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
            And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
          have realClassifier :
              RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
                (BHist.e1 (BHist.e1 BHist.Empty)) := by
            unfold HilbertSingletonInnerProduct
            exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
          exact And.intro carrierM
            (And.intro carrierN
              (And.intro sameMEmpty (And.intro sameNEmpty realClassifier)))

theorem HilbertSingletonProjection_residual_decomposition {h p residual : BHist} :
    VecSpaceSingletonCarrier h -> VecSpaceSingletonClassifier p BHist.Empty ->
      Cont p residual h ->
        VecSpaceSingletonClassifier residual BHist.Empty ∧
          RealConstantHistoryClassifier (NormSingletonNorm residual)
            (BHist.e1 (BHist.e1 BHist.Empty)) ∧
            RealConstantHistoryClassifier (HilbertSingletonInnerProduct residual BHist.Empty)
              (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierH _classifiedP projectionContinuation
  have emptyResult : Cont p residual BHist.Empty :=
    cont_result_hsame_transport projectionContinuation carrierH
  have residualEmpty : hsame residual BHist.Empty :=
    (cont_empty_result_inversion emptyResult).right
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have residualClassified : VecSpaceSingletonClassifier residual BHist.Empty :=
    And.intro residualEmpty (And.intro emptyCarrier residualEmpty)
  have emptyClassified : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have normClassified :
      RealConstantHistoryClassifier (NormSingletonNorm residual)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    (NormSingletonEmptyHistory_zero_exactness residualEmpty).mpr residualClassified
  have innerRows :=
    HilbertSingleton_constant_inner_product_transport residualClassified emptyClassified
  exact And.intro residualClassified (And.intro normClassified innerRows.left)

theorem HilbertSingleton_endpoint_readback {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          MetricDistanceWitness m n BHist.Empty := by
  intro carrierM carrierN
  have normRows := NormSingletonEmptyHistory_laws carrierM carrierN
  have innerRows := HilbertSingleton_inner_product_norm_compatibility carrierM
  have mEndpoint : hsame m BHist.Empty := normRows.right.right.right.left.right.right
  have nEndpoint : hsame n BHist.Empty := normRows.right.right.right.right.right.right
  have distanceWitness : MetricDistanceWitness m n BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := m) (y := n)).mpr
      (And.intro mEndpoint nEndpoint)
  have innerConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr innerRows.right normRows.right.right.right.left
  exact And.intro normRows.right.left (And.intro innerConstant distanceWitness)

theorem HilbertSingleton_projection_carried_endpoint {h : BHist} :
    VecSpaceSingletonCarrier h ->
      VecSpaceSingletonCarrier BHist.Empty ∧
        VecSpaceSingletonClassifier h BHist.Empty ∧
          RealConstantHistoryClassifier (NormSingletonNorm BHist.Empty)
            (BHist.e1 (BHist.e1 BHist.Empty)) ∧
            RealConstantHistoryClassifier (NormSingletonNorm h)
              (BHist.e1 (BHist.e1 BHist.Empty)) ∧
              RealConstantHistoryClassifier (HilbertSingletonInnerProduct h BHist.Empty)
                (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierH
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have normEmpty := NormSingletonEmptyHistory_laws emptyCarrier emptyCarrier
  have normH := NormSingletonEmptyHistory_laws carrierH emptyCarrier
  have hEmpty : VecSpaceSingletonClassifier h BHist.Empty := normH.right.right.right.left
  have emptyClassified :
      VecSpaceSingletonClassifier BHist.Empty BHist.Empty := normEmpty.right.right.right.left
  have innerRows :=
    HilbertSingleton_constant_inner_product_transport hEmpty emptyClassified
  exact And.intro emptyCarrier
    (And.intro hEmpty
      (And.intro normEmpty.right.left
        (And.intro normH.right.left innerRows.left)))

theorem HilbertSingleton_projection_residual_decomposition {h p : BHist} :
    VecSpaceSingletonCarrier h -> VecSpaceSingletonClassifier p BHist.Empty ->
      VecSpaceSingletonClassifier h p ∧
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul h p) BHist.Empty ∧
          RealConstantHistoryClassifier (HilbertSingletonInnerProduct h p) (NormSingletonNorm p) := by
  intro carrierH classifiedP
  have carrierP : VecSpaceSingletonCarrier p := classifiedP.left
  have normRows := NormSingletonEmptyHistory_laws carrierH carrierP
  have hP : VecSpaceSingletonClassifier h p :=
    And.intro carrierH
      (And.intro carrierP (hsame_trans carrierH (hsame_symm carrierP)))
  have smulEmpty : VecSpaceSingletonClassifier (VecSpaceSingletonSmul h p) BHist.Empty :=
    normRows.right.right.left
  have innerRows := HilbertSingleton_constant_inner_product_transport hP classifiedP
  have innerNorm :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct h p) (NormSingletonNorm p) :=
    by
      unfold NormSingletonNorm
      exact innerRows.left
  exact And.intro hP (And.intro smulEmpty innerNorm)

def HilbertSingletonProjectionWitness (m p : BHist) : Prop :=
  VecSpaceSingletonCarrier m ∧
    VecSpaceSingletonCarrier p ∧
      VecSpaceSingletonClassifier p BHist.Empty ∧
        RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          RealConstantHistoryClassifier (HilbertSingletonInnerProduct m p)
            (BHist.e1 (BHist.e1 BHist.Empty))

def HilbertSingletonProjection (_h : BHist) : BHist :=
  BHist.Empty

theorem HilbertSingletonProjection_existence {m : BHist} :
    VecSpaceSingletonCarrier m ->
      HilbertSingletonProjectionWitness m BHist.Empty ∧
        VecSpaceSingletonClassifier (HilbertSingletonProjection m) BHist.Empty := by
  intro carrierM
  have projectionRows := HilbertSingleton_projection_carried_endpoint carrierM
  have emptyClassified : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro projectionRows.left
      (And.intro projectionRows.left (hsame_refl BHist.Empty))
  have projectionWitness : HilbertSingletonProjectionWitness m BHist.Empty :=
    And.intro carrierM
      (And.intro projectionRows.left
        (And.intro emptyClassified
          (And.intro projectionRows.right.right.right.left projectionRows.right.right.right.right)))
  have projectionClassified :
      VecSpaceSingletonClassifier (HilbertSingletonProjection m) BHist.Empty := by
    unfold HilbertSingletonProjection
    exact emptyClassified
  exact And.intro projectionWitness projectionClassified

theorem HilbertSingletonProjection_idempotence {h : BHist} :
    VecSpaceSingletonCarrier h ->
      VecSpaceSingletonClassifier (HilbertSingletonProjection (HilbertSingletonProjection h))
          (HilbertSingletonProjection h) ∧
        RealConstantHistoryClassifier
          (HilbertSingletonInnerProduct (HilbertSingletonProjection h)
            (HilbertSingletonProjection (HilbertSingletonProjection h)))
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro _carrierH
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have projectionClassified :
      VecSpaceSingletonClassifier (HilbertSingletonProjection (HilbertSingletonProjection h))
        (HilbertSingletonProjection h) := by
    unfold HilbertSingletonProjection
    exact And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have innerRows :=
    HilbertSingleton_constant_inner_product_transport projectionClassified projectionClassified
  exact And.intro projectionClassified innerRows.left

theorem HilbertSingletonProjection_residual_zero_package {h : BHist} :
    VecSpaceSingletonCarrier h ->
      VecSpaceSingletonClassifier (HilbertSingletonProjection (HilbertSingletonProjection h))
          (HilbertSingletonProjection h) ∧
        RealConstantHistoryClassifier (NormSingletonNorm (HilbertSingletonProjection h))
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          RealConstantHistoryClassifier
            (NormSingletonNorm (HilbertSingletonProjection (HilbertSingletonProjection h)))
            (BHist.e1 (BHist.e1 BHist.Empty)) ∧
            RealConstantHistoryClassifier
              (HilbertSingletonInnerProduct h (HilbertSingletonProjection h))
              (NormSingletonNorm (HilbertSingletonProjection h)) := by
  intro carrierH
  have idempotenceRows := HilbertSingletonProjection_idempotence carrierH
  have projectionCarrier : VecSpaceSingletonCarrier (HilbertSingletonProjection h) := by
    unfold HilbertSingletonProjection
    exact hsame_refl BHist.Empty
  have projectionProjectionCarrier :
      VecSpaceSingletonCarrier (HilbertSingletonProjection (HilbertSingletonProjection h)) := by
    unfold HilbertSingletonProjection
    exact hsame_refl BHist.Empty
  have normProjectionRows :=
    NormSingletonEmptyHistory_laws projectionCarrier projectionProjectionCarrier
  have normProjectedRows :=
    NormSingletonEmptyHistory_laws projectionProjectionCarrier projectionCarrier
  have projectionClassified : VecSpaceSingletonClassifier (HilbertSingletonProjection h) BHist.Empty := by
    unfold HilbertSingletonProjection
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have decompositionRows :=
    HilbertSingleton_projection_residual_decomposition carrierH projectionClassified
  exact And.intro idempotenceRows.left
    (And.intro normProjectionRows.right.left
      (And.intro normProjectedRows.right.left decompositionRows.right.right))

theorem HilbertSingletonProjection_witness_idempotent {m p : BHist} :
    HilbertSingletonProjectionWitness m p ->
      HilbertSingletonProjectionWitness p BHist.Empty ∧
        VecSpaceSingletonClassifier (HilbertSingletonProjection p) p := by
  intro projectionWitness
  have carrierP : VecSpaceSingletonCarrier p := projectionWitness.right.left
  have endpointP : VecSpaceSingletonClassifier p BHist.Empty := projectionWitness.right.right.left
  have projectionRows := HilbertSingleton_projection_carried_endpoint carrierP
  have emptyClassified : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro projectionRows.left (And.intro projectionRows.left (hsame_refl BHist.Empty))
  have emptyProjectionWitness :
      HilbertSingletonProjectionWitness p BHist.Empty :=
    And.intro carrierP
      (And.intro projectionRows.left
        (And.intro emptyClassified
          (And.intro projectionRows.right.right.right.left projectionRows.right.right.right.right)))
  have projectionClassified :
      VecSpaceSingletonClassifier (HilbertSingletonProjection p) p := by
    unfold HilbertSingletonProjection
    exact And.intro endpointP.right.left
      (And.intro carrierP (hsame_symm endpointP.right.right))
  exact And.intro emptyProjectionWitness projectionClassified

theorem HilbertSingletonProjection_semantic_name_certificate :
    SemanticNameCert VecSpaceSingletonCarrier
      (fun h : BHist => VecSpaceSingletonClassifier (HilbertSingletonProjection h) BHist.Empty)
      (fun h : BHist =>
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct h (HilbertSingletonProjection h))
          (BHist.e1 (BHist.e1 BHist.Empty)))
      VecSpaceSingletonClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h carrierH
        exact And.intro carrierH (And.intro carrierH (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k l classifiedHK classifiedKL
        exact And.intro classifiedHK.left
          (And.intro classifiedKL.right.left
            (hsame_trans classifiedHK.right.right classifiedKL.right.right))
      carrier_respects_equiv := by
        intro _h _k classified _carrierH
        exact classified.right.left
    }
    pattern_sound := by
      intro h carrierH
      have endpoint := HilbertSingletonProjection_carried_endpoint carrierH
      unfold HilbertSingletonProjection
      exact And.intro endpoint.left
        (And.intro endpoint.left (hsame_refl BHist.Empty))
    ledger_sound := by
      intro h carrierH
      have endpoint := HilbertSingletonProjection_carried_endpoint carrierH
      unfold HilbertSingletonProjection
      exact endpoint.right.right.right
  }

theorem HilbertSingletonProjection_orthogonal_zero {m p n : BHist} :
    HilbertSingletonProjectionWitness m p -> VecSpaceSingletonCarrier n ->
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct (VecSpaceSingletonSmul m p) n)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro projectionWitness carrierN
  have smulClassified :
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul m p) BHist.Empty :=
    (HilbertSingleton_projection_residual_decomposition projectionWitness.left
      projectionWitness.right.right.left).right.left
  have nClassified : VecSpaceSingletonClassifier n BHist.Empty :=
    And.intro carrierN
      (And.intro (hsame_refl BHist.Empty) carrierN)
  exact (HilbertSingleton_constant_inner_product_transport smulClassified nClassified).left

theorem HilbertSingletonProjection_uniqueness {m p q : BHist} :
    HilbertSingletonProjectionWitness m p -> HilbertSingletonProjectionWitness m q ->
      VecSpaceSingletonClassifier p q ∧
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct p q)
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro projectionP projectionQ
  have pClassified : VecSpaceSingletonClassifier p BHist.Empty :=
    projectionP.right.right.left
  have qClassified : VecSpaceSingletonClassifier q BHist.Empty :=
    projectionQ.right.right.left
  have pQClassified : VecSpaceSingletonClassifier p q :=
    And.intro pClassified.left
      (And.intro qClassified.left (hsame_trans pClassified.right.right (hsame_symm qClassified.left)))
  have innerRows := HilbertSingleton_constant_inner_product_transport pQClassified pQClassified
  exact And.intro pQClassified innerRows.left

end BEDC.Derived.HilbertUp
