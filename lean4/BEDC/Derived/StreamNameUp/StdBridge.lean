import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameUp_StdBridge {s t : BHist -> BHist} {bundle : ProbeBundle BHist} :
    RatStreamNameClassifier s t ->
      RatStreamNameFiniteWindowClassifier s t bundle ∧
        (forall n : BHist, UnaryHistory n -> RatHistoryCarrier (s n)) ∧
          (forall n : BHist, InBundle n bundle -> UnaryHistory n ->
            RatHistoryClassifier (s n) (t n)) := by
  intro classified
  exact And.intro
    (fun n _member nUnary => classified.right.right n nUnary)
    (And.intro classified.left
      (fun n _member nUnary => classified.right.right n nUnary))

end BEDC.Derived.StreamNameUp
