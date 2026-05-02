import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MetricDistanceWitness_triangle_append_closed {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dxyz (append x dyz) := by
  intro xy yz xyz
  have xyRel : Cont x y dxy := xy.right.right.right
  have yzRel : Cont y z dyz := yz.right.right.right
  have xyzRel : Cont dxy z dxyz := xyz.right.right.right
  cases xyRel
  cases yzRel
  cases xyzRel
  exact append_assoc x y z

end BEDC.Derived.MetricUp
