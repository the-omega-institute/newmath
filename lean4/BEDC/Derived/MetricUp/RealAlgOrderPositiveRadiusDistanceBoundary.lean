import BEDC.Derived.MetricUp.Transport

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricRealAlgOrder_positive_radius_distance_boundary {left right positive distance : BHist} :
    UnaryHistory left → UnaryHistory right → UnaryHistory positive → Cont left right distance →
      hsame distance positive → MetricDistanceWitness left right positive := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame MetricDistanceWitness
  intro leftUnary rightUnary positiveUnary distanceCont sameDistance
  exact
    And.intro leftUnary
      (And.intro rightUnary
        (And.intro positiveUnary
          (cont_result_hsame_transport distanceCont sameDistance)))

end BEDC.Derived.MetricUp
