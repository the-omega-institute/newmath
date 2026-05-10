import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamName_successor_reindexing_stability {s t : BHist -> BHist}
    {bundle : ProbeBundle BHist} :
    RatStreamNameCarrier s -> RatStreamNameClassifier s t ->
      RatStreamNameCarrier (fun n => s (BHist.e1 n)) ∧
        RatStreamNameClassifier (fun n => s (BHist.e1 n)) (fun n => t (BHist.e1 n)) ∧
          RatStreamNameFiniteWindowClassifier (fun n => s (BHist.e1 n))
            (fun n => t (BHist.e1 n)) bundle := by
  intro carrierS classified
  have stability :=
    RatStreamName_reindexing_and_map_stability
      (s := s) (t := t) (r := fun n : BHist => BHist.e1 n) (F := fun h : BHist => h)
      (fun n nUnary => unary_e1_closed nUnary)
      (fun h carrier => carrier)
      (fun h k pointClassified => pointClassified)
  have successorCarrier : RatStreamNameCarrier (fun n => s (BHist.e1 n)) :=
    stability.left carrierS
  have successorClassifier :
      RatStreamNameClassifier (fun n => s (BHist.e1 n)) (fun n => t (BHist.e1 n)) :=
    stability.right.left classified
  have finiteWindow :
      RatStreamNameFiniteWindowClassifier (fun n => s (BHist.e1 n))
        (fun n => t (BHist.e1 n)) bundle := by
    intro n _member nUnary
    exact successorClassifier.right.right n nUnary
  exact And.intro successorCarrier (And.intro successorClassifier finiteWindow)

end BEDC.Derived.StreamNameUp
