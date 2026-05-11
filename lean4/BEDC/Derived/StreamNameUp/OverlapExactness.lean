import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameConstantWindow_overlap_exactness {h k : BHist}
    {left right overlap : ProbeBundle BHist} :
    (exists n : BHist, InBundle n overlap ∧ UnaryHistory n) ->
      (forall n : BHist, InBundle n overlap -> InBundle n left) ->
        (forall n : BHist, InBundle n overlap -> InBundle n right) ->
          RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) left ->
            RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) right ->
              RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) overlap ∧
                RatHistoryClassifier h k := by
  intro overlapWitness overlapLeft overlapRight leftClassified rightClassified
  have overlapFromLeft :
      RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) overlap := by
    intro n member nUnary
    exact leftClassified n (overlapLeft n member) nUnary
  have overlapFromRight :
      RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) overlap := by
    intro n member nUnary
    exact rightClassified n (overlapRight n member) nUnary
  have exactness :=
    RatStreamNameFiniteWindowClassifier_constant_exactness
      (h := h) (k := k) (bundle := overlap) overlapWitness
  have ratClassified : RatHistoryClassifier h k :=
    Iff.mp exactness overlapFromRight
  exact And.intro overlapFromLeft ratClassified

end BEDC.Derived.StreamNameUp
