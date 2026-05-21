import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricPatternSpecification (x y d publicRead : BHist) : Prop :=
  MetricDistanceWitness x y d ∧ Cont d publicRead (append d publicRead)

theorem MetricPatternSpecification_result_unary {x y d publicRead : BHist} :
    MetricPatternSpecification x y d publicRead -> UnaryHistory publicRead ->
      UnaryHistory (append d publicRead) ∧ Cont d publicRead (append d publicRead) := by
  intro pattern publicCarrier
  exact And.intro (unary_append_closed pattern.left.right.right.left publicCarrier) pattern.right

end BEDC.Derived.MetricUp
