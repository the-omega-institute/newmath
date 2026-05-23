import BEDC.Derived.MetricUp.DepthZero
import BEDC.Derived.MetricUp.BoundaryExactness
import BEDC.Derived.MetricUp.HsameDeterminism
import BEDC.Derived.MetricUp.Transport

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

theorem MetricDistanceWitness_visible_context_triangle_append_closed {p q x y z dxy dyz dxyz :
    BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        hsame dxyz (append x dyz) := by
  intro visible yz xyz
  have visibleData :
      UnaryHistory p ∧ UnaryHistory q ∧ MetricDistanceWitness x y dxy :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp visible
  exact MetricDistanceWitness_triangle_append_closed visibleData.right.right yz xyz

theorem MetricDistanceWitness_composite_endpoint_hsame_append_result
    {x x' y y' z z' dxy dxyz : BHist} :
    hsame x x' -> hsame y y' -> hsame z z' ->
      MetricDistanceWitness x y dxy -> MetricDistanceWitness dxy z dxyz ->
        hsame dxyz (append x' (append y' z')) := by
  intro sameX sameY sameZ xy xyz
  cases sameX
  cases sameY
  cases sameZ
  have xyRel : Cont x y dxy := xy.right.right.right
  have xyzRel : Cont dxy z dxyz := xyz.right.right.right
  cases xyRel
  cases xyzRel
  exact append_assoc x y z

theorem MetricDistanceWitness_triangle_cont_middle_closed {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz -> Cont dxy z dxyz ->
      MetricDistanceWitness x dyz dxyz := by
  intro xy yz xyzRel
  have xyRel : Cont x y dxy := xy.right.right.right
  have yzRel : Cont y z dyz := yz.right.right.right
  exact And.intro xy.left
    (And.intro yz.right.right.left
      (And.intro (unary_cont_closed xy.right.right.left yz.right.left xyzRel)
        (by
          cases xyRel
          cases yzRel
          cases xyzRel
          exact cont_intro (append_assoc x y z))))

theorem MetricDistanceWitness_visible_context_triangle_cont_middle_closed
    {p q x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness y z dyz -> Cont dxy z dxyz ->
        MetricDistanceWitness x dyz dxyz := by
  intro visible yz middleContinuation
  have visibleData :
      UnaryHistory p ∧ UnaryHistory q ∧ MetricDistanceWitness x y dxy :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp visible
  exact MetricDistanceWitness_triangle_cont_middle_closed visibleData.right.right yz
    middleContinuation

theorem MetricDistanceWitness_triangle_cont_middle_result_deterministic
    {x y z dxy dyz dxyz displayed : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz -> Cont dxy z dxyz ->
      MetricDistanceWitness x dyz displayed -> hsame dxyz displayed := by
  intro xy yz middleContinuation displayedWitness
  have canonical : MetricDistanceWitness x dyz dxyz :=
    MetricDistanceWitness_triangle_cont_middle_closed xy yz middleContinuation
  exact cont_deterministic canonical.right.right.right displayedWitness.right.right.right

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

theorem MetricspaceVisibleContextTriangleBoundary {p q x y z dxy dyz dxyz : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> Cont x z dxyz ->
        MetricDistanceWitness (append p x) (append z q) (append (append p dxyz) q) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro pCarrier qCarrier xy yz xzContinuation
  have central : MetricDistanceWitness x z dxyz :=
    And.intro xy.left
      (And.intro yz.right.left
        (And.intro (unary_cont_closed xy.left yz.right.left xzContinuation) xzContinuation))
  exact
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := z)
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

theorem MetricDistanceWitness_triangle_append_context_source_deterministic
    {p q x x' y z dxy dyz dxyz : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        MetricDistanceWitness (append p x') (append dyz q) (append (append p dxyz) q) ->
          hsame x x' := by
  intro pCarrier qCarrier xy yz xyz displayedWitness
  have canonical :
      MetricDistanceWitness (append p x) (append dyz q) (append (append p dxyz) q) :=
    MetricDistanceWitness_triangle_append_context_closed pCarrier qCarrier xy yz xyz
  exact MetricDistanceWitness_visible_context_hsame_source_deterministic (hsame_refl dyz)
    (hsame_refl dxyz) canonical displayedWitness

theorem MetricDistanceWitness_triangle_append_context_endpoint_deterministic
    {p q x x' y z dxy dyz dxyz e : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        (MetricDistanceWitness (append p x') (append dyz q) (append (append p dxyz) q) ->
          hsame x x') /\
        (MetricDistanceWitness (append p x) (append e q) (append (append p dxyz) q) ->
          hsame dyz e) := by
  intro pCarrier qCarrier xy yz xyz
  constructor
  · intro displayed
    exact MetricDistanceWitness_triangle_append_context_source_deterministic
      pCarrier qCarrier xy yz xyz displayed
  · intro displayed
    have canonical :
        MetricDistanceWitness (append p x) (append dyz q) (append (append p dxyz) q) :=
      MetricDistanceWitness_triangle_append_context_closed pCarrier qCarrier xy yz xyz
    exact MetricDistanceWitness_visible_context_target_deterministic canonical displayed

theorem MetricDistanceWitness_triangle_append_context_endpoint_transport
    {p q x x' y z dxy dyz dxyz e : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        hsame x x' -> hsame dyz e ->
          MetricDistanceWitness (append p x') (append e q) (append (append p dxyz) q) := by
  intro pCarrier qCarrier xy yz xyz sameX sameDyz
  have canonical :
      MetricDistanceWitness (append p x) (append dyz q) (append (append p dxyz) q) :=
    MetricDistanceWitness_triangle_append_context_closed pCarrier qCarrier xy yz xyz
  have sameSource : hsame (append p x) (append p x') := by
    cases sameX
    exact hsame_refl (append p x)
  have sameTarget : hsame (append dyz q) (append e q) := by
    cases sameDyz
    exact hsame_refl (append dyz q)
  exact MetricDistanceWitness_hsame_fields_transport sameSource sameTarget
    (hsame_refl (append (append p dxyz) q)) canonical

theorem MetricDistanceWitness_triangle_append_context_endpoint_iff
    {p q x x' y z dxy dyz dxyz e : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        (MetricDistanceWitness (append p x') (append dyz q) (append (append p dxyz) q) ↔
          hsame x x') /\
        (MetricDistanceWitness (append p x) (append e q) (append (append p dxyz) q) ↔
          hsame dyz e) := by
  -- BEDC touchpoint anchor: BHist hsame MetricDistanceWitness
  intro pCarrier qCarrier xy yz xyz
  constructor
  · constructor
    · intro displayed
      exact MetricDistanceWitness_triangle_append_context_source_deterministic
        pCarrier qCarrier xy yz xyz displayed
    · intro sameX
      exact MetricDistanceWitness_triangle_append_context_endpoint_transport
        pCarrier qCarrier xy yz xyz sameX (hsame_refl dyz)
  · constructor
    · intro displayed
      have canonical :
          MetricDistanceWitness (append p x) (append dyz q) (append (append p dxyz) q) :=
        MetricDistanceWitness_triangle_append_context_closed pCarrier qCarrier xy yz xyz
      exact MetricDistanceWitness_visible_context_target_deterministic canonical displayed
    · intro sameDyz
      exact MetricDistanceWitness_triangle_append_context_endpoint_transport
        pCarrier qCarrier xy yz xyz (hsame_refl x) sameDyz

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

theorem MetricDistanceWitness_triangle_left_distance_empty_collapse {x y z dxy dyz dxyz :
    BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dxy BHist.Empty ->
        hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame dxyz z ∧ hsame dyz z := by
  intro xy yz xyz dxyEmpty
  cases dxyEmpty
  have xyEndpoints : hsame x BHist.Empty ∧ hsame y BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := x) (y := y)).mp xy
  have dxyzExact : hsame dxyz z :=
    (MetricDistanceWitness_empty_left_iff (y := z) (d := dxyz)).mp xyz |>.right
  have dyzExact : hsame dyz z := by
    cases xyEndpoints.right
    exact (MetricDistanceWitness_empty_left_iff (y := z) (d := dyz)).mp yz |>.right
  exact And.intro xyEndpoints.left
    (And.intro xyEndpoints.right (And.intro dxyzExact dyzExact))

theorem MetricDistanceWitness_triangle_left_distance_empty_visible_context_closed
    {p q x y z dxy dyz dxyz : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        hsame dxy BHist.Empty ->
          MetricDistanceWitness (append p BHist.Empty) (append z q)
            (append (append p dxyz) q) := by
  intro pCarrier qCarrier xy yz xyz dxyEmpty
  have collapse :=
    MetricDistanceWitness_triangle_left_distance_empty_collapse xy yz xyz dxyEmpty
  have central : MetricDistanceWitness BHist.Empty z dxyz :=
    (MetricDistanceWitness_empty_left_iff (y := z) (d := dxyz)).mpr
      (And.intro yz.right.left collapse.right.right.left)
  exact
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := BHist.Empty)
      (y := z) (d := dxyz)).mpr
      (And.intro pCarrier (And.intro qCarrier central))

theorem MetricDistanceWitness_triangle_left_empty_boundary_witness {x y z dxy dyz dxyz :
    BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dxy BHist.Empty ->
        MetricDistanceWitness BHist.Empty z dxyz := by
  intro xy yz xyz dxyEmpty
  have collapsed :
      hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame dxyz z ∧ hsame dyz z :=
    MetricDistanceWitness_triangle_left_distance_empty_collapse xy yz xyz dxyEmpty
  exact (MetricDistanceWitness_empty_left_iff (y := z) (d := dxyz)).mpr
    (And.intro yz.right.left collapsed.right.right.left)

theorem MetricDistanceWitness_triangle_right_distance_empty_collapse {x y z dxy dyz dxyz :
    BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dyz BHist.Empty ->
        hsame y BHist.Empty ∧ hsame z BHist.Empty ∧ hsame dxy x ∧ hsame dxyz x := by
  intro xy yz xyz dyzEmpty
  cases dyzEmpty
  have yzEndpoints : hsame y BHist.Empty ∧ hsame z BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := y) (y := z)).mp yz
  have dxyExact : hsame dxy x := by
    cases yzEndpoints.left
    exact (MetricDistanceWitness_empty_right_iff (x := x) (d := dxy)).mp xy |>.right
  have dxyzExactDxy : hsame dxyz dxy := by
    cases yzEndpoints.right
    exact (MetricDistanceWitness_empty_right_iff (x := dxy) (d := dxyz)).mp xyz |>.right
  exact And.intro yzEndpoints.left
    (And.intro yzEndpoints.right
      (And.intro dxyExact (hsame_trans dxyzExactDxy dxyExact)))

theorem MetricDistanceWitness_triangle_right_distance_empty_visible_context_closed
    {p q x y z dxy dyz dxyz : BHist} :
    UnaryHistory p -> UnaryHistory q -> MetricDistanceWitness x y dxy ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        hsame dyz BHist.Empty ->
          MetricDistanceWitness (append p x) (append BHist.Empty q)
            (append (append p dxyz) q) := by
  intro pCarrier qCarrier xy yz xyz dyzEmpty
  have collapse :=
    MetricDistanceWitness_triangle_right_distance_empty_collapse xy yz xyz dyzEmpty
  have central : MetricDistanceWitness x BHist.Empty dxyz :=
    (MetricDistanceWitness_empty_right_iff (x := x) (d := dxyz)).mpr
      (And.intro xy.left collapse.right.right.right)
  exact
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x)
      (y := BHist.Empty) (d := dxyz)).mpr
      (And.intro pCarrier (And.intro qCarrier central))

theorem MetricDistanceWitness_triangle_right_distance_empty_spine_witness
    {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dyz BHist.Empty ->
        MetricDistanceWitness x BHist.Empty dxyz := by
  intro xy yz xyz dyzEmpty
  have collapse :=
    MetricDistanceWitness_triangle_right_distance_empty_collapse xy yz xyz dyzEmpty
  exact (MetricDistanceWitness_empty_right_iff (x := x) (d := dxyz)).mpr
    (And.intro xy.left collapse.right.right.right)

theorem MetricDistanceWitness_triangle_right_empty_boundary_witness {x y z dxy dyz dxyz :
    BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dyz BHist.Empty ->
        MetricDistanceWitness x BHist.Empty dxyz := by
  intro xy yz xyz dyzEmpty
  have collapsed :
      hsame y BHist.Empty ∧ hsame z BHist.Empty ∧ hsame dxy x ∧ hsame dxyz x :=
    MetricDistanceWitness_triangle_right_distance_empty_collapse xy yz xyz dyzEmpty
  have canonical : MetricDistanceWitness x BHist.Empty x :=
    And.intro xy.left
      (And.intro unary_empty (And.intro xy.left (cont_right_unit x)))
  exact MetricDistanceWitness_hsame_fields_transport (hsame_refl x) (hsame_refl BHist.Empty)
    (hsame_symm collapsed.right.right.right) canonical

theorem MetricDistanceWitness_triangle_bilateral_empty_edge_collapse
    {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dxy BHist.Empty ->
        hsame dyz BHist.Empty ->
          hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame z BHist.Empty ∧
            hsame dxyz BHist.Empty ∧ MetricDistanceDepth dxyz = 0 ∧
              MetricDistanceWitness BHist.Empty BHist.Empty dxyz := by
  intro xy yz xyz dxyEmpty dyzEmpty
  have leftCollapse :
      hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame dxyz z ∧ hsame dyz z :=
    MetricDistanceWitness_triangle_left_distance_empty_collapse xy yz xyz dxyEmpty
  have rightCollapse :
      hsame y BHist.Empty ∧ hsame z BHist.Empty ∧ hsame dxy x ∧ hsame dxyz x :=
    MetricDistanceWitness_triangle_right_distance_empty_collapse xy yz xyz dyzEmpty
  have xEmpty : hsame x BHist.Empty := leftCollapse.left
  have yEmpty : hsame y BHist.Empty := leftCollapse.right.left
  have zEmpty : hsame z BHist.Empty := rightCollapse.right.left
  have dxyzEmpty : hsame dxyz BHist.Empty :=
    hsame_trans leftCollapse.right.right.left zEmpty
  have depthZero : MetricDistanceDepth dxyz = 0 :=
    MetricDistanceDepth_zero_iff_empty.mpr dxyzEmpty
  have emptyWitness : MetricDistanceWitness BHist.Empty BHist.Empty dxyz :=
    MetricDistanceWitness_hsame_fields_transport (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) (hsame_symm dxyzEmpty)
      ((MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
  exact And.intro xEmpty
    (And.intro yEmpty
      (And.intro zEmpty
        (And.intro dxyzEmpty (And.intro depthZero emptyWitness))))

theorem MetricDistanceWitness_two_sided_empty_triangle_witness_exactness
    {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dxy BHist.Empty ->
        hsame dyz BHist.Empty ->
          hsame dxyz BHist.Empty ∧ MetricDistanceWitness BHist.Empty BHist.Empty dxyz ∧
            MetricDistanceWitness BHist.Empty z dxyz ∧
              MetricDistanceWitness x BHist.Empty dxyz := by
  intro xy yz xyz dxyEmpty dyzEmpty
  have collapsed :=
    MetricDistanceWitness_triangle_bilateral_empty_edge_collapse xy yz xyz dxyEmpty dyzEmpty
  have leftBoundary :
      MetricDistanceWitness BHist.Empty z dxyz :=
    MetricDistanceWitness_triangle_left_empty_boundary_witness xy yz xyz dxyEmpty
  have rightBoundary :
      MetricDistanceWitness x BHist.Empty dxyz :=
    MetricDistanceWitness_triangle_right_empty_boundary_witness xy yz xyz dyzEmpty
  exact And.intro collapsed.right.right.right.left
    (And.intro collapsed.right.right.right.right.right
      (And.intro leftBoundary rightBoundary))

theorem MetricDistanceWitness_two_sided_empty_triangle_boundary_package
    {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> hsame dxy BHist.Empty ->
        hsame dyz BHist.Empty ->
          hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame z BHist.Empty ∧
            hsame dxyz BHist.Empty ∧ MetricDistanceWitness BHist.Empty BHist.Empty dxyz := by
  intro xy yz xyz dxyEmpty dyzEmpty
  have leftCollapse :
      hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame dxyz z ∧ hsame dyz z :=
    MetricDistanceWitness_triangle_left_distance_empty_collapse xy yz xyz dxyEmpty
  have rightCollapse :
      hsame y BHist.Empty ∧ hsame z BHist.Empty ∧ hsame dxy x ∧ hsame dxyz x :=
    MetricDistanceWitness_triangle_right_distance_empty_collapse xy yz xyz dyzEmpty
  have dxyzEmpty : hsame dxyz BHist.Empty :=
    hsame_trans leftCollapse.right.right.left rightCollapse.right.left
  have emptyWitness : MetricDistanceWitness BHist.Empty BHist.Empty dxyz :=
    MetricDistanceWitness_hsame_fields_transport (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) (hsame_symm dxyzEmpty)
      ((MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
  exact And.intro leftCollapse.left
    (And.intro leftCollapse.right.left
      (And.intro rightCollapse.right.left (And.intro dxyzEmpty emptyWitness)))

theorem MetricDistanceWitness_visible_context_triangle_depth_zero_collapse
    {p q x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        MetricDistanceDepth dxyz = 0 ->
          hsame dxyz (append x dyz) ∧ hsame x BHist.Empty ∧ hsame y BHist.Empty ∧
            hsame z BHist.Empty ∧ hsame dxy BHist.Empty ∧ hsame dyz BHist.Empty := by
  intro visible yz xyz depthZero
  have visibleData :
      UnaryHistory p ∧ UnaryHistory q ∧ MetricDistanceWitness x y dxy :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp visible
  exact MetricDistanceWitness_triangle_depth_zero_collapse visibleData.right.right yz xyz
    depthZero

theorem MetricDistanceWitness_triangle_depth_zero_iff_empty_spine {x y z dxy dyz dxyz :
    BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz ->
        (MetricDistanceDepth dxyz = 0 ↔
          hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame z BHist.Empty ∧
            hsame dxy BHist.Empty ∧ hsame dyz BHist.Empty) := by
  intro xy yz xyz
  constructor
  · intro depthZero
    exact (MetricDistanceWitness_triangle_depth_zero_collapse xy yz xyz depthZero).right
  · intro emptySpine
    exact MetricDistanceWitness_empty_endpoints_depth_zero xyz emptySpine.right.right.right.left
      emptySpine.right.right.left

theorem MetricDistanceWitness_visible_context_triangle_depth_zero_iff_empty_spine
    {p q x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        (MetricDistanceDepth dxyz = 0 ↔
          hsame x BHist.Empty ∧ hsame y BHist.Empty ∧ hsame z BHist.Empty ∧
            hsame dxy BHist.Empty ∧ hsame dyz BHist.Empty) := by
  intro visible yz xyz
  have visibleData :
      UnaryHistory p ∧ UnaryHistory q ∧ MetricDistanceWitness x y dxy :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp visible
  exact MetricDistanceWitness_triangle_depth_zero_iff_empty_spine visibleData.right.right yz xyz

theorem MetricDistanceWitness_triangle_nonempty_endpoint_nonempty {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> (hsame dxyz BHist.Empty -> False) ->
        (hsame x BHist.Empty -> False) ∨ (hsame y BHist.Empty -> False) ∨
          (hsame z BHist.Empty -> False) := by
  intro xy _yz xyz nonemptyDxyz
  have outerEndpoints :=
    MetricDistanceWitness_nonempty_distance_endpoint_nonempty xyz nonemptyDxyz
  cases outerEndpoints with
  | inl nonemptyDxy =>
      have leftEndpoints :=
        MetricDistanceWitness_nonempty_distance_endpoint_nonempty xy nonemptyDxy
      cases leftEndpoints with
      | inl nonemptyX =>
          exact Or.inl nonemptyX
      | inr nonemptyY =>
          exact Or.inr (Or.inl nonemptyY)
  | inr nonemptyZ =>
      exact Or.inr (Or.inr nonemptyZ)

theorem MetricDistanceWitness_triangle_nonempty_spine_e1_endpoint_cases
    {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz -> (hsame dxyz BHist.Empty -> False) ->
        (∃ x0 : BHist, x = BHist.e1 x0 ∧ UnaryHistory x0) ∨
          (∃ y0 : BHist, y = BHist.e1 y0 ∧ UnaryHistory y0) ∨
            (∃ z0 : BHist, z = BHist.e1 z0 ∧ UnaryHistory z0) := by
  intro xy yz xyz nonemptyDxyz
  have endpoints :=
    MetricDistanceWitness_triangle_nonempty_endpoint_nonempty xy yz xyz nonemptyDxyz
  cases endpoints with
  | inl nonemptyX =>
      exact Or.inl (unary_history_nonempty_e1_tail xy.left nonemptyX)
  | inr endpointRest =>
      cases endpointRest with
      | inl nonemptyY =>
          exact Or.inr (Or.inl (unary_history_nonempty_e1_tail yz.left nonemptyY))
      | inr nonemptyZ =>
          exact Or.inr (Or.inr (unary_history_nonempty_e1_tail yz.right.left nonemptyZ))

theorem MetricDistanceWitness_triangle_nonempty_spine_iff_nonempty_distance
    {x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y z dyz ->
      MetricDistanceWitness dxy z dxyz ->
        ((hsame dxyz BHist.Empty -> False) ↔
          (hsame x BHist.Empty -> False) ∨ (hsame y BHist.Empty -> False) ∨
            (hsame z BHist.Empty -> False) ∨ (hsame dxy BHist.Empty -> False) ∨
              (hsame dyz BHist.Empty -> False)) := by
  intro xy yz xyz
  constructor
  · intro nonemptyDistance
    have endpoints :=
      MetricDistanceWitness_triangle_nonempty_endpoint_nonempty xy yz xyz nonemptyDistance
    cases endpoints with
    | inl nonemptyX =>
        exact Or.inl nonemptyX
    | inr endpointRest =>
        cases endpointRest with
        | inl nonemptyY =>
            exact Or.inr (Or.inl nonemptyY)
        | inr nonemptyZ =>
            exact Or.inr (Or.inr (Or.inl nonemptyZ))
  · intro nonemptySpine
    intro emptyDistance
    have depthZero : MetricDistanceDepth dxyz = 0 :=
      MetricDistanceDepth_zero_iff_empty.mpr emptyDistance
    have emptySpine :=
      (MetricDistanceWitness_triangle_depth_zero_iff_empty_spine xy yz xyz).mp depthZero
    cases nonemptySpine with
    | inl nonemptyX =>
        exact nonemptyX emptySpine.left
    | inr spineRest =>
        cases spineRest with
        | inl nonemptyY =>
            exact nonemptyY emptySpine.right.left
        | inr spineRest =>
            cases spineRest with
            | inl nonemptyZ =>
                exact nonemptyZ emptySpine.right.right.left
            | inr spineRest =>
                cases spineRest with
                | inl nonemptyDxy =>
                    exact nonemptyDxy emptySpine.right.right.right.left
                | inr nonemptyDyz =>
                    exact nonemptyDyz emptySpine.right.right.right.right

theorem MetricDistanceWitness_visible_context_triangle_nonempty_spine_iff_nonempty_distance
    {p q x y z dxy dyz dxyz : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness y z dyz -> MetricDistanceWitness dxy z dxyz ->
        ((hsame dxyz BHist.Empty -> False) ↔
          (hsame x BHist.Empty -> False) ∨ (hsame y BHist.Empty -> False) ∨
            (hsame z BHist.Empty -> False) ∨ (hsame dxy BHist.Empty -> False) ∨
              (hsame dyz BHist.Empty -> False)) := by
  intro visible yz xyz
  have visibleData :
      UnaryHistory p ∧ UnaryHistory q ∧ MetricDistanceWitness x y dxy :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp visible
  exact MetricDistanceWitness_triangle_nonempty_spine_iff_nonempty_distance
    visibleData.right.right yz xyz

end BEDC.Derived.MetricUp
