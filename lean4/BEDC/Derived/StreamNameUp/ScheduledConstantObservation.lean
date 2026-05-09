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

theorem RatStreamName_scheduled_window_reindex_stability {d e : BHist}
    {r q u : BHist -> BHist} :
    RatHistoryCarrier d -> RatHistoryClassifier d e ->
      (forall n : BHist, UnaryHistory n -> UnaryHistory (u n)) ->
        RatStreamNameCarrier (fun n : BHist => RatConstStream d (r (u n))) ∧
          RatStreamNameClassifier (fun n : BHist => RatConstStream d (r (u n)))
            (fun n : BHist => RatConstStream e (q (u n))) ∧
            (forall {n : BHist}, UnaryHistory n ->
              RatHistoryClassifier (RatConstStream d (r (u n)))
                (RatConstStream e (q (u n)))) := by
  intro carrierD classifiedDE uUnary
  have carrierE : RatHistoryCarrier e := classifiedDE.right.left
  have streamCarrier :
      RatStreamNameCarrier (fun n : BHist => RatConstStream d (r (u n))) := by
    intro n nUnary
    have _windowUnary : UnaryHistory (u n) := uUnary n nUnary
    change RatHistoryCarrier d
    exact carrierD
  have streamCarrierE :
      RatStreamNameCarrier (fun n : BHist => RatConstStream e (q (u n))) := by
    intro n nUnary
    have _windowUnary : UnaryHistory (u n) := uUnary n nUnary
    change RatHistoryCarrier e
    exact carrierE
  have pointRows :
      forall {n : BHist}, UnaryHistory n ->
        RatHistoryClassifier (RatConstStream d (r (u n))) (RatConstStream e (q (u n))) := by
    intro n nUnary
    have _windowUnary : UnaryHistory (u n) := uUnary n nUnary
    change RatHistoryClassifier d e
    exact classifiedDE
  exact And.intro streamCarrier
    (And.intro (And.intro streamCarrier
        (And.intro streamCarrierE (fun n nUnary => pointRows (n := n) nUnary)))
      pointRows)

end BEDC.Derived.StreamNameUp
