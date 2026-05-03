import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

theorem MetricDistanceWitness_triangle_append_context_closed {p q x y z dxy dyz dxyz : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        MetricDistanceWitness (append p x) (append dyz q) (append (append p dxyz) q) := by
  intro pCarrier qCarrier xy yz xyz
  have central : MetricDistanceWitness x dyz dxyz :=
    And.intro xy.left
      (And.intro yz.right.right.left
        (And.intro xyz.right.right.left
          (MetricDistanceWitness_triangle_append_closed xy yz xyz)))
  exact
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := dyz)
      (d := dxyz)).mpr
      (And.intro pCarrier (And.intro qCarrier central))

theorem MetricDistanceWitness_triangle_append_context_result_deterministic
    {p q x y z dxy dyz dxyz displayed : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        MetricDistanceWitness (append p x) (append dyz q) displayed ->
          hsame displayed (append (append p dxyz) q) := by
  intro pCarrier qCarrier xy yz xyz displayedWitness
  have canonical :
      MetricDistanceWitness (append p x) (append dyz q) (append (append p dxyz) q) :=
    MetricDistanceWitness_triangle_append_context_closed pCarrier qCarrier xy yz xyz
  exact cont_deterministic displayedWitness.right.right.right canonical.right.right.right

end BEDC.Derived.MetricUp
