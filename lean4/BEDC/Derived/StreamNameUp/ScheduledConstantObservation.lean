import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamName_scheduled_constant_observation_exactness {d e : BHist}
    {r q : BHist -> BHist} :
    RatHistoryCarrier d -> RatHistoryClassifier d e ->
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) ∧
        RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
          (fun n : BHist => RatConstStream e (q n)) ∧
          (forall {n : BHist}, UnaryHistory n ->
            RatHistoryClassifier (RatConstStream d (r n)) (RatConstStream e (q n))) := by
  intro carrierD classifiedDE
  have exactness :=
    RatStreamName_independent_reindexed_constant_point_exactness
      (h := d) (k := e) (r := r) (q := q)
  have streamCarrier :
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r n)) :=
    Iff.mpr exactness.left carrierD
  have streamClassifier :
      RatStreamNameClassifier (fun n : BHist => RatConstStream d (r n))
        (fun n : BHist => RatConstStream e (q n)) :=
    Iff.mpr exactness.right classifiedDE
  have pointRows :
      forall {n : BHist}, UnaryHistory n ->
        RatHistoryClassifier (RatConstStream d (r n)) (RatConstStream e (q n)) := by
    intro n _nUnary
    change RatHistoryClassifier d e
    exact classifiedDE
  exact And.intro streamCarrier (And.intro streamClassifier pointRows)

end BEDC.Derived.StreamNameUp
