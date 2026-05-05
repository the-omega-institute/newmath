import BEDC.Derived.CompleteMetricUp

namespace BEDC.Derived.BanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CompleteMetricUp
open BEDC.Derived.MetricUp
open BEDC.Derived.RatUp

theorem BanachSingleton_complete_metric_limit_empty_witness {s M : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) BHist.Empty) ->
      (forall {n : BHist}, UnaryHistory n ->
        RatHistoryClassifier BHist.Empty (M n)) ->
        CompleteMetricLimitWitness (fun h : BHist => hsame h BHist.Empty) s M
          BHist.Empty := by
  intro streamEmpty modulusClassified
  constructor
  · exact hsame_refl BHist.Empty
  · intro n nUnary sourceEmpty
    have distanceWitness : MetricDistanceWitness (s n) BHist.Empty BHist.Empty :=
      (MetricDistanceWitness_empty_distance_iff (x := s n) (y := BHist.Empty)).mpr
        (And.intro sourceEmpty (hsame_refl BHist.Empty))
    have continuation : Cont (s n) BHist.Empty BHist.Empty := by
      exact cont_right_unit_iff.mpr (hsame_symm sourceEmpty)
    exact Exists.intro BHist.Empty
      (And.intro distanceWitness (And.intro continuation (modulusClassified nUnary)))

end BEDC.Derived.BanachUp
