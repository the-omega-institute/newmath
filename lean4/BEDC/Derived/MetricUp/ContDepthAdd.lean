import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_cont_depth_add {x y z dxy dxyz : BHist} :
    MetricDistanceWitness x y dxy -> UnaryHistory z -> Cont dxy z dxyz ->
      MetricDistanceDepth dxyz =
        MetricDistanceDepth x + MetricDistanceDepth y + MetricDistanceDepth z := by
  intro witness zCarrier tailRel
  have dxyCarrier : UnaryHistory dxy := witness.right.right.left
  have tailWitness : MetricDistanceWitness dxy z dxyz :=
    And.intro dxyCarrier
      (And.intro zCarrier (And.intro (unary_cont_closed dxyCarrier zCarrier tailRel) tailRel))
  have firstDepth := MetricDistanceWitness_depth_add witness
  have totalDepth := MetricDistanceWitness_depth_add tailWitness
  rw [totalDepth, firstDepth, Nat.add_assoc]

end BEDC.Derived.MetricUp
