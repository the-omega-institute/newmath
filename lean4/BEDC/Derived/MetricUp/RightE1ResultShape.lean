import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_right_e1_result_shape {x y d : BHist} :
    MetricDistanceWitness x (BHist.e1 y) d ->
      ∃ k : BHist, hsame d (BHist.e1 k) ∧ MetricDistanceWitness x y k := by
  intro witness
  cases witness with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro _dCarrier distance =>
              have yTailCarrier : UnaryHistory y := unary_e1_inversion yCarrier
              exact Exists.intro (append x y)
                (And.intro distance
                  (And.intro xCarrier
                    (And.intro yTailCarrier
                      (And.intro (unary_append_closed xCarrier yTailCarrier) (cont_intro rfl)))))

end BEDC.Derived.MetricUp
