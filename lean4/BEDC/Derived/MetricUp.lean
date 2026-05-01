import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricDistanceWitness (x y dist : BHist) : Prop :=
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory dist ∧ Cont x y dist

theorem MetricDistanceWitness_symmetric_classifier {x y dxy dyx : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y x dyx -> hsame dxy dyx := by
  intro forward reverse
  exact unary_continuation_commutativity forward.1 forward.2.1 forward.2.2.2 reverse.2.2.2

end BEDC.Derived.MetricUp
