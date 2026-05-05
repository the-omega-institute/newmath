import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.ContinuousUp.Transport
import BEDC.Derived.MetricUp.Transport

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_hsame_field_transport_depth
    {source source' map map' target target' modulus modulus' cert cert' distance distance' :
      BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      hsame source source' ->
        hsame map map' ->
          hsame target target' ->
            hsame modulus modulus' ->
              hsame cert cert' ->
                hsame distance distance' ->
                  ContinuousMapCarrier source' map' target' modulus' cert' distance' ∧
                    Cont source' target' distance' ∧
                      MetricDistanceDepth distance' =
                        MetricDistanceDepth source' + MetricDistanceDepth target' := by
  intro carrier sameSource sameMap sameTarget sameModulus sameCert sameDistance
  have functionCarrier :
      ContinuousFunctionCarrier source' map' target' modulus' cert' :=
    ContinuousFunctionCarrier_hsame_transport sameSource sameMap sameTarget sameModulus
      sameCert carrier.left
  have distanceCarrier :
      MetricDistanceWitness source' target' distance' :=
    MetricDistanceWitness_hsame_fields_transport sameSource sameTarget sameDistance carrier.right
  have distanceDepth :
      Cont source' target' distance' ∧
        MetricDistanceDepth distance' = MetricDistanceDepth source' + MetricDistanceDepth target' :=
    MetricDistanceWitness_hsame_transport_cont_depth_add sameSource sameTarget sameDistance
      carrier.right
  exact And.intro (And.intro functionCarrier distanceCarrier) distanceDepth

end BEDC.Derived.ContinuousMapUp
