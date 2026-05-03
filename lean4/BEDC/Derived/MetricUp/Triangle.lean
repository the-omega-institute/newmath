import BEDC.Derived.MetricUp.DepthZero

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

theorem MetricDistanceWitness_triangle_append_depth_add {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz ->
        hsame dxyz (append x dyz) ∧
          MetricDistanceDepth dxyz = MetricDistanceDepth x + MetricDistanceDepth dyz := by
  intro xy yz xyz
  have sameAppend : hsame dxyz (append x dyz) :=
    MetricDistanceWitness_triangle_append_closed xy yz xyz
  have central : MetricDistanceWitness x dyz dxyz :=
    And.intro xy.left
      (And.intro yz.right.right.left (And.intro xyz.right.right.left sameAppend))
  exact And.intro sameAppend (MetricDistanceWitness_depth_add central)

theorem MetricDistanceWitness_triangle_depth_zero_collapse {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> MetricDistanceDepth dxyz = 0 ->
        hsame dxyz (append x dyz) ∧ hsame x BHist.Empty ∧ hsame y BHist.Empty ∧
          hsame z BHist.Empty ∧ hsame dxy BHist.Empty ∧ hsame dyz BHist.Empty := by
  intro xy yz xyz depthZero
  have sameAppend : hsame dxyz (append x dyz) :=
    MetricDistanceWitness_triangle_append_closed xy yz xyz
  have central : MetricDistanceWitness x dyz dxyz :=
    And.intro xy.left
      (And.intro yz.right.right.left (And.intro xyz.right.right.left sameAppend))
  have centralEndpoints := MetricDistanceWitness_depth_zero_empty_endpoints central depthZero
  have xEmpty : hsame x BHist.Empty := centralEndpoints.left
  have dyzEmpty : hsame dyz BHist.Empty := centralEndpoints.right
  have yzEndpoints : hsame y BHist.Empty ∧ hsame z BHist.Empty := by
    cases dyzEmpty
    exact MetricDistanceWitness_empty_distance_iff.mp yz
  have yEmpty : hsame y BHist.Empty := yzEndpoints.left
  have zEmpty : hsame z BHist.Empty := yzEndpoints.right
  have dxyEmpty : hsame dxy BHist.Empty := by
    cases xEmpty
    cases yEmpty
    cases xy.right.right.right
    rfl
  exact And.intro sameAppend
    (And.intro xEmpty
      (And.intro yEmpty
        (And.intro zEmpty (And.intro dxyEmpty dyzEmpty))))

end BEDC.Derived.MetricUp
