import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatStreamNameFiniteWindowClassifier_bundle_union_handoff {s t : BHist -> BHist}
    {left right : ProbeBundle BHist} :
    RatStreamNameFiniteWindowClassifier s t left ->
      RatStreamNameFiniteWindowClassifier s t right ->
        RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) ∧
          (RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) ->
            RatStreamNameFiniteWindowClassifier s t left ∧
              RatStreamNameFiniteWindowClassifier s t right) := by
  intro classifiedLeft classifiedRight
  constructor
  · intro n member nUnary
    cases Iff.mp inBundle_bundleAppend_iff member with
    | inl memberLeft =>
        exact classifiedLeft n memberLeft nUnary
    | inr memberRight =>
        exact classifiedRight n memberRight nUnary
  · intro classifiedUnion
    constructor
    · intro n memberLeft nUnary
      exact classifiedUnion n (Iff.mpr inBundle_bundleAppend_iff (Or.inl memberLeft))
        nUnary
    · intro n memberRight nUnary
      exact classifiedUnion n (Iff.mpr inBundle_bundleAppend_iff (Or.inr memberRight))
        nUnary

end BEDC.Derived.StreamNameUp
