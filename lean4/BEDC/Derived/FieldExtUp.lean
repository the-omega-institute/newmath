import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp

def FieldExtSingletonEmbedding (h : BHist) : BHist :=
  append BHist.Empty h

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

end BEDC.Derived.FieldExtUp
