import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatStreamNameFiniteWindowClassifier_structural_laws {s t : BHist -> BHist}
    {left right : ProbeBundle BHist} :
    (forall {n : BHist}, InBundle n right -> InBundle n left) ->
      RatStreamNameFiniteWindowClassifier s t left ->
        (RatStreamNameFiniteWindowClassifier s t right) ∧
          (RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) ->
            RatStreamNameFiniteWindowClassifier s t left ∧
              RatStreamNameFiniteWindowClassifier s t right) ∧
            (RatStreamNameFiniteWindowClassifier s t left ->
              RatStreamNameFiniteWindowClassifier s t right ->
                RatStreamNameFiniteWindowClassifier s t (bundleAppend left right)) := by
  intro rightSubbundle leftClassified
  have rightClassified : RatStreamNameFiniteWindowClassifier s t right := by
    intro n memberRight nUnary
    exact leftClassified n (rightSubbundle memberRight) nUnary
  have appendedProjection :
      RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) ->
        RatStreamNameFiniteWindowClassifier s t left ∧
          RatStreamNameFiniteWindowClassifier s t right := by
    intro appendedClassified
    constructor
    · intro n memberLeft nUnary
      have memberAppended : InBundle n (bundleAppend left right) :=
        Iff.mpr inBundle_bundleAppend_iff (Or.inl memberLeft)
      exact appendedClassified n memberAppended nUnary
    · intro n memberRight nUnary
      have memberAppended : InBundle n (bundleAppend left right) :=
        Iff.mpr inBundle_bundleAppend_iff (Or.inr memberRight)
      exact appendedClassified n memberAppended nUnary
  have appendedRecomposition :
      RatStreamNameFiniteWindowClassifier s t left ->
        RatStreamNameFiniteWindowClassifier s t right ->
          RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) := by
    intro classifiedLeft classifiedRight n memberAppended nUnary
    cases Iff.mp inBundle_bundleAppend_iff memberAppended with
    | inl memberLeft =>
        exact classifiedLeft n memberLeft nUnary
    | inr memberRight =>
        exact classifiedRight n memberRight nUnary
  exact And.intro rightClassified
    (And.intro appendedProjection appendedRecomposition)

end BEDC.Derived.StreamNameUp
