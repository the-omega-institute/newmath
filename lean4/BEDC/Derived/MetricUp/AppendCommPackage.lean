import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_unary_append_comm_package {x y : BHist} :
    UnaryHistory x -> UnaryHistory y ->
      MetricDistanceWitness (append x y) (append y x) (append (append x y) (append y x)) ∧
        hsame (append x y) (append y x) := by
  intro xCarrier yCarrier
  have leftCarrier : UnaryHistory (append x y) := unary_append_closed xCarrier yCarrier
  have rightCarrier : UnaryHistory (append y x) := unary_append_closed yCarrier xCarrier
  exact And.intro
    (And.intro leftCarrier
      (And.intro rightCarrier
        (And.intro (unary_append_closed leftCarrier rightCarrier) (cont_intro rfl))))
    (unary_append_comm_hsame xCarrier yCarrier)

end BEDC.Derived.MetricUp
