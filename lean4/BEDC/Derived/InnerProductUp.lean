import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.InnerProductUp

open BEDC.FKernel.NameCert
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

def InnerProductSingletonForm (_x _y : BHist) : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

def InnerProductSingletonOrthogonal (x y : BHist) : Prop :=
  VecSpaceSingletonCarrier x ∧ VecSpaceSingletonCarrier y ∧
    RealConstantHistoryClassifier (InnerProductSingletonForm x y)
      (BHist.e1 (BHist.e1 BHist.Empty))

theorem InnerProductSingletonOrthogonal_zero_left {y : BHist} :
    VecSpaceSingletonCarrier y ->
      InnerProductSingletonOrthogonal BHist.Empty y ∧
        RealConstantHistoryClassifier (InnerProductSingletonForm BHist.Empty y)
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierY
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm BHist.Empty y)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro (And.intro emptyCarrier (And.intro carrierY realClassifier)) realClassifier

theorem InnerProductSingletonOrthogonal_zero_right {x : BHist} :
    VecSpaceSingletonCarrier x ->
      InnerProductSingletonOrthogonal x BHist.Empty ∧
        RealConstantHistoryClassifier (InnerProductSingletonForm x BHist.Empty)
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierX
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm x BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro (And.intro carrierX (And.intro emptyCarrier realClassifier)) realClassifier

theorem InnerProductSingletonOrthogonal_transport {x y x' y' : BHist} :
    VecSpaceSingletonClassifier x x' -> VecSpaceSingletonClassifier y y' ->
      InnerProductSingletonOrthogonal x y ->
        InnerProductSingletonOrthogonal x' y' ∧
          RealConstantHistoryClassifier (InnerProductSingletonForm x' y')
            (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro sameXX' sameYY' _orthogonal
  have carrierX' : VecSpaceSingletonCarrier x' := sameXX'.right.left
  have carrierY' : VecSpaceSingletonCarrier y' := sameYY'.right.left
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm x' y')
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro (And.intro carrierX' (And.intro carrierY' realClassifier))
    realClassifier

theorem InnerProductSingletonOrthogonal_symm_constant_endpoint {x y : BHist} :
    InnerProductSingletonOrthogonal x y ->
      InnerProductSingletonOrthogonal y x ∧
        RealConstantHistoryClassifier (InnerProductSingletonForm y x)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          hsame (InnerProductSingletonForm y x) (InnerProductSingletonForm x y) := by
  intro orthogonal
  have sameY : VecSpaceSingletonClassifier y y :=
    And.intro orthogonal.right.left
      (And.intro orthogonal.right.left (hsame_refl y))
  have sameX : VecSpaceSingletonClassifier x x :=
    And.intro orthogonal.left
      (And.intro orthogonal.left (hsame_refl x))
  have symmOrthogonal : InnerProductSingletonOrthogonal y x := by
    have realClassifier :
        RealConstantHistoryClassifier (InnerProductSingletonForm y x)
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
      unfold InnerProductSingletonForm
      exact orthogonal.right.right
    exact And.intro orthogonal.right.left (And.intro orthogonal.left realClassifier)
  have transported := InnerProductSingletonOrthogonal_transport sameY sameX symmOrthogonal
  have sameForms :
      hsame (InnerProductSingletonForm y x) (InnerProductSingletonForm x y) := by
    unfold InnerProductSingletonForm
    exact hsame_refl (BHist.e1 (BHist.e1 BHist.Empty))
  exact And.intro transported.left (And.intro transported.right sameForms)

theorem InnerProductSingletonDiagonal_zero_exactness {x : BHist} :
    VecSpaceSingletonCarrier x ->
      (RealConstantHistoryClassifier (InnerProductSingletonForm x x)
          (BHist.e1 (BHist.e1 BHist.Empty)) ↔ VecSpaceSingletonClassifier x BHist.Empty) := by
  intro carrierX
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · intro _realClassifier
    exact And.intro carrierX (And.intro emptyCarrier carrierX)
  · intro _classified
    have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
      RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
    have ratClassifier :
        RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
      And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier

theorem InnerProductSingleton_semanticNameCert :
    SemanticNameCert VecSpaceSingletonCarrier
      (fun h : BHist => InnerProductSingletonOrthogonal h BHist.Empty)
      (fun h : BHist =>
        RealConstantHistoryClassifier (InnerProductSingletonForm h h)
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
      exact (InnerProductSingletonOrthogonal_zero_right (x := h) carrierH).left
    ledger_sound := by
      intro h carrierH
      exact (InnerProductSingletonDiagonal_zero_exactness (x := h) carrierH).mpr
        (And.intro carrierH (And.intro (hsame_refl BHist.Empty) carrierH))
  }

theorem InnerProductRoot_vecspace_scalar_exposure {x y : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y ->
      VecSpaceSingletonCarrier x ∧ VecSpaceSingletonCarrier y ∧
        RealConstantHistoryClassifier (InnerProductSingletonForm x y)
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierX carrierY
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm x y)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro carrierX (And.intro carrierY realClassifier)

theorem InnerProductSingletonOrthogonal_symm_package {x y : BHist} :
    InnerProductSingletonOrthogonal x y ->
      InnerProductSingletonOrthogonal y x ∧
        RealConstantHistoryClassifier (InnerProductSingletonForm y x)
          (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro orthogonal
  have carrierX : VecSpaceSingletonCarrier x := orthogonal.left
  have carrierY : VecSpaceSingletonCarrier y := orthogonal.right.left
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm y x)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro (And.intro carrierY (And.intro carrierX realClassifier)) realClassifier

theorem InnerProductRootHilbert_consumption_surface {x y : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y ->
      InnerProductSingletonOrthogonal BHist.Empty x ∧
        InnerProductSingletonOrthogonal y BHist.Empty ∧
          InnerProductSingletonOrthogonal x y ∧
            RealConstantHistoryClassifier (InnerProductSingletonForm x y)
              (BHist.e1 (BHist.e1 BHist.Empty)) ∧
              SemanticNameCert VecSpaceSingletonCarrier
                (fun h : BHist => InnerProductSingletonOrthogonal h BHist.Empty)
                (fun h : BHist =>
                  RealConstantHistoryClassifier (InnerProductSingletonForm h h)
                    (BHist.e1 (BHist.e1 BHist.Empty)))
                VecSpaceSingletonClassifier := by
  intro carrierX carrierY
  have zeroLeft := InnerProductSingletonOrthogonal_zero_left (y := x) carrierX
  have zeroRight := InnerProductSingletonOrthogonal_zero_right (x := y) carrierY
  have exposure := InnerProductRoot_vecspace_scalar_exposure carrierX carrierY
  have orthogonalXY : InnerProductSingletonOrthogonal x y :=
    And.intro exposure.left (And.intro exposure.right.left exposure.right.right)
  exact And.intro zeroLeft.left
    (And.intro zeroRight.left
      (And.intro orthogonalXY
        (And.intro exposure.right.right InnerProductSingleton_semanticNameCert)))

end BEDC.Derived.InnerProductUp
