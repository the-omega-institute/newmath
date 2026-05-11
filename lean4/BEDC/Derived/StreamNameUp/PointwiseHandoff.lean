import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamNameFiniteWindowClassifier_pointwise_hsame_closure
    {s t s' t' : BHist -> BHist} {bundle : ProbeBundle BHist} :
    (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> RatHistoryCarrier (s n)) ->
      RatStreamNameFiniteWindowClassifier s t bundle ->
        (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> hsame (s n) (s' n)) ->
          (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> hsame (t n) (t' n)) ->
            RatStreamNameFiniteWindowClassifier s' t' bundle ∧
              (forall {n : BHist}, InBundle n bundle -> UnaryHistory n ->
                RatHistoryCarrier (s' n) ∧ RatHistoryCarrier (t' n)) := by
  intro sourceCarrier classifier sameSource sameTarget
  constructor
  · intro n member nUnary
    exact RatHistoryClassifier_hsame_transport (sameSource member nUnary) (sameTarget member nUnary)
      (classifier n member nUnary)
  · intro n member nUnary
    have targetCarrier : RatHistoryCarrier (t n) :=
      (classifier n member nUnary).right.left
    exact ⟨RatHistoryCarrier_hsame_transport (sameSource member nUnary) (sourceCarrier member nUnary),
      RatHistoryCarrier_hsame_transport (sameTarget member nUnary) targetCarrier⟩

theorem RatStreamNameFiniteWindowClassifier_real_regseq_handoff
    {s t : BHist -> BHist} {bundle : ProbeBundle BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      forall {n : BHist}, InBundle n bundle -> UnaryHistory n ->
        RatHistoryClassifier (s n) (t n) ∧
          PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) ∧
            UnaryHistory (s n) ∧ UnaryHistory (t n) := by
  intro classified n member nUnary
  have selected : RatHistoryClassifier (s n) (t n) :=
    classified n member nUnary
  have positives : PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) :=
    RatHistoryClassifier_positive_denominators selected
  have leftRows := PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows := PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact ⟨selected, positives.left, positives.right, leftRows.left, rightRows.left⟩

theorem RatStreamNameFiniteWindowClassifier_singleton_diagonal_handoff
    {s t : BHist -> BHist} {n : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n ->
      RatStreamNameFiniteWindowClassifier s t (ProbeBundle.Bcons n ProbeBundle.Bnil) ∧
        InBundle n (ProbeBundle.Bcons n ProbeBundle.Bnil) ∧
          RatHistoryClassifier (s n) (t n) := by
  intro classified nUnary
  have selected : RatHistoryClassifier (s n) (t n) :=
    classified.right.right n nUnary
  have singletonMember : InBundle n (ProbeBundle.Bcons n ProbeBundle.Bnil) :=
    inBundle_cons_self n ProbeBundle.Bnil
  have windowClassified :
      RatStreamNameFiniteWindowClassifier s t (ProbeBundle.Bcons n ProbeBundle.Bnil) := by
    intro m member mUnary
    have sameMN : m = n :=
      inBundle_singleton_iff.mp member
    cases sameMN
    exact classified.right.right n mUnary
  exact And.intro windowClassified (And.intro singletonMember selected)

end BEDC.Derived.StreamNameUp
