import BEDC.Derived.RHRoute.CausalReflectionPositiveCone
import BEDC.Derived.RHRoute.PrimeCausalTower
import BEDC.Derived.RHRoute.ThreeAxisOrbitCollapse
import BEDC.Derived.RHRoute.ZetaUnitaryScaleClosure

namespace BEDC.Derived.RHRoute.AnalyticGombocForXi

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.CausalReflectionPositiveCone
open BEDC.Derived.RHRoute.PrimeCausalTower
open BEDC.Derived.RHRoute.BoxKernelConcrete

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

/-
Analytic Gomboc for xi is recorded here as a conditional proof shape.
The Pick, Herglotz, and Stieltjes surfaces are the classical hard frontier:
their equivalence for completed xi, and their equivalence with the classical
RH reading, is not proved in this module.  The checked content is the
zero-extra-logical interface and the conditional handoff to `ConstructiveRH`.

Excluded routes:
* local zero-side containers that patch isolated holes,
* hidden positive real scaling such as an `exp(-rh) * r` ballast term,
* termwise search over zeros or coefficients.

The intended route is source-side global positivity tied to the prime-causal
tower, with no backward use of the desired critical-axis conclusion.
-/

def StrictRightOfCriticalLine (s : RatComplex) : Prop :=
  ratLt halfRat s.re

structure PickHilbertDecomposition where
  cone : CausalReflectionPositiveCone
  Phi : RatComplex -> cone.H.H
  phi_reads_crpc_eta : forall z : RatComplex, Phi z = cone.eta z
  kernel_eq :
    forall z w : RatComplex,
      RatComplexEq (cone.E.K_E z w) (cone.H.inner (Phi w) (Phi z))
  no_negative_length_sq :
    forall packet : KernelGramPacket,
      ratLe ratZero (kernelQuadratic cone.H Phi packet)
  crpc_frontier_scope :
    cone.inhabitant_frontier_obligations =
      canonicalInhabitantFrontierObligations

theorem pick_kernel_positive
    (A : PickHilbertDecomposition) :
    KernelPositive A.cone.H A.Phi := by
  intro packet
  exact A.no_negative_length_sq packet

theorem rh_from_pick_hilbert_decomposition
    (A : PickHilbertDecomposition) :
    ConstructiveRH := by
  exact CRPC_implies_RH A.cone

inductive HerglotzReadbackObligation where
  | completedXiLogDerivative
  | rightHalfPlaneNoPole
  | positiveRealPartBoundary

def canonicalHerglotzReadbackObligations :
    List HerglotzReadbackObligation :=
  [ HerglotzReadbackObligation.completedXiLogDerivative,
    HerglotzReadbackObligation.rightHalfPlaneNoPole,
    HerglotzReadbackObligation.positiveRealPartBoundary ]

structure HerglotzPositivity where
  xi_log_derivative_real_part : RatComplex -> Rat
  source_side_readback_obligations : List HerglotzReadbackObligation
  source_side_readback_scope :
    source_side_readback_obligations =
      canonicalHerglotzReadbackObligations
  no_illegal_scale_source_sink :
    forall s : RatComplex,
      StrictRightOfCriticalLine s ->
        ratLe ratZero (xi_log_derivative_real_part s)
  right_half_plane_scope :
    forall s : RatComplex,
      StrictRightOfCriticalLine s ->
        ratLe ratZero (xi_log_derivative_real_part s)

theorem herglotz_positive_on_right_half_plane
    (B : HerglotzPositivity)
    (s : RatComplex)
    (hs : StrictRightOfCriticalLine s) :
    ratLe ratZero (B.xi_log_derivative_real_part s) := by
  exact B.right_half_plane_scope s hs

theorem herglotz_readback_obligation_count
    (B : HerglotzPositivity) :
    B.source_side_readback_obligations.length = 3 := by
  rw [B.source_side_readback_scope]
  rfl

inductive StieltjesReadbackObligation where
  | completedXiHalfSqrtLogDerivative
  | cauchyKernelInverseXPlusT
  | locatedPositiveMeasure

def canonicalStieltjesReadbackObligations :
    List StieltjesReadbackObligation :=
  [ StieltjesReadbackObligation.completedXiHalfSqrtLogDerivative,
    StieltjesReadbackObligation.cauchyKernelInverseXPlusT,
    StieltjesReadbackObligation.locatedPositiveMeasure ]

structure LocatedPositiveSpectralMeasure where
  Atom : Type
  mass : Atom -> Rat
  spectral_location : Atom -> Rat
  mass_nonnegative : forall a : Atom, ratLe ratZero (mass a)
  location_nonnegative :
    forall a : Atom, ratLe ratZero (spectral_location a)
  cauchy_kernel : Rat -> Atom -> Rat
  kernel_nonnegative :
    forall x : Rat,
      ratLe ratZero x ->
        forall a : Atom, ratLe ratZero (cauchy_kernel x a)
  integral : Rat -> Rat
  integral_nonnegative :
    forall x : Rat, ratLe ratZero x -> ratLe ratZero (integral x)
  readback_obligations : List StieltjesReadbackObligation
  readback_obligations_scope :
    readback_obligations = canonicalStieltjesReadbackObligations

theorem spectral_measure_readback_obligation_count
    (M : LocatedPositiveSpectralMeasure) :
    M.readback_obligations.length = 3 := by
  rw [M.readback_obligations_scope]
  rfl

structure StieltjesPositiveSpectral where
  spectral_measure : LocatedPositiveSpectralMeasure
  dlog_xi_half_sqrt : Rat -> Rat
  stieltjes_readback :
    forall x : Rat,
      ratLe ratZero x ->
        RatEq (dlog_xi_half_sqrt x) (spectral_measure.integral x)
  positive_spectral_measure :
    forall a : spectral_measure.Atom,
      ratLe ratZero (spectral_measure.mass a)

theorem stieltjes_derivative_nonnegative
    (C : StieltjesPositiveSpectral)
    (x : Rat)
    (hx : ratLe ratZero x) :
    ratLe ratZero (C.dlog_xi_half_sqrt x) := by
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    (C.spectral_measure.integral_nonnegative x hx)
    (RatEq_symm (C.stieltjes_readback x hx))

inductive AnalyticGombocHardBoundary where
  | pickHerglotzEquivalence
  | herglotzStieltjesNevanlinna
  | stieltjesPickDeBranges
  | classicalRHEquivalence
  | locatedXiReadback

def canonicalAnalyticGombocHardBoundaries :
    List AnalyticGombocHardBoundary :=
  [ AnalyticGombocHardBoundary.pickHerglotzEquivalence,
    AnalyticGombocHardBoundary.herglotzStieltjesNevanlinna,
    AnalyticGombocHardBoundary.stieltjesPickDeBranges,
    AnalyticGombocHardBoundary.classicalRHEquivalence,
    AnalyticGombocHardBoundary.locatedXiReadback ]

structure AnalyticGombocEquivalenceBridge where
  hard_boundaries : List AnalyticGombocHardBoundary
  hard_boundaries_scope :
    hard_boundaries = canonicalAnalyticGombocHardBoundaries
  A_to_B : PickHilbertDecomposition -> HerglotzPositivity
  B_to_C : HerglotzPositivity -> StieltjesPositiveSpectral
  C_to_A : StieltjesPositiveSpectral -> PickHilbertDecomposition

inductive PickHerglotzReductionObligation where
  | cayleyTransformRightHalfPlane
  | pickKernelKolmogorovFactor
  | herglotzRealPartReadback
  | locatedBoundaryControl

def canonicalPickHerglotzReductionObligations :
    List PickHerglotzReductionObligation :=
  [ PickHerglotzReductionObligation.cayleyTransformRightHalfPlane,
    PickHerglotzReductionObligation.pickKernelKolmogorovFactor,
    PickHerglotzReductionObligation.herglotzRealPartReadback,
    PickHerglotzReductionObligation.locatedBoundaryControl ]

structure PickHerglotzReduction where
  obligations : List PickHerglotzReductionObligation
  obligations_scope :
    obligations = canonicalPickHerglotzReductionObligations
  from_pick : PickHilbertDecomposition -> HerglotzPositivity
  from_herglotz_to_pick : HerglotzPositivity -> PickHilbertDecomposition

theorem pick_herglotz_reduction_obligation_count
    (R : PickHerglotzReduction) :
    R.obligations.length = 4 := by
  rw [R.obligations_scope]
  rfl

def pick_to_herglotz_reduction
    (R : PickHerglotzReduction)
    (A : PickHilbertDecomposition) :
    HerglotzPositivity :=
  R.from_pick A

def herglotz_to_pick_reduction
    (R : PickHerglotzReduction)
    (B : HerglotzPositivity) :
    PickHilbertDecomposition :=
  R.from_herglotz_to_pick B

theorem pick_herglotz_interderivable
    (R : PickHerglotzReduction) :
    (Nonempty PickHilbertDecomposition -> Nonempty HerglotzPositivity) ∧
      (Nonempty HerglotzPositivity -> Nonempty PickHilbertDecomposition) := by
  constructor
  · intro hA
    cases hA with
    | intro A =>
        exact ⟨R.from_pick A⟩
  · intro hB
    cases hB with
    | intro B =>
        exact ⟨R.from_herglotz_to_pick B⟩

theorem pick_herglotz_nonempty_iff
    (R : PickHerglotzReduction) :
    Iff (Nonempty PickHilbertDecomposition) (Nonempty HerglotzPositivity) := by
  have AB := pick_herglotz_interderivable R
  exact Iff.intro AB.left AB.right

inductive HerglotzStieltjesReductionObligation where
  | nevanlinnaRepresentation
  | positiveSpectralMeasure
  | cauchyStieltjesKernelReadback
  | locatedIntegralControl

def canonicalHerglotzStieltjesReductionObligations :
    List HerglotzStieltjesReductionObligation :=
  [ HerglotzStieltjesReductionObligation.nevanlinnaRepresentation,
    HerglotzStieltjesReductionObligation.positiveSpectralMeasure,
    HerglotzStieltjesReductionObligation.cauchyStieltjesKernelReadback,
    HerglotzStieltjesReductionObligation.locatedIntegralControl ]

structure HerglotzStieltjesReduction where
  obligations : List HerglotzStieltjesReductionObligation
  obligations_scope :
    obligations = canonicalHerglotzStieltjesReductionObligations
  from_herglotz : HerglotzPositivity -> StieltjesPositiveSpectral
  from_stieltjes_to_herglotz : StieltjesPositiveSpectral -> HerglotzPositivity

theorem herglotz_stieltjes_reduction_obligation_count
    (R : HerglotzStieltjesReduction) :
    R.obligations.length = 4 := by
  rw [R.obligations_scope]
  rfl

def herglotz_to_stieltjes_reduction
    (R : HerglotzStieltjesReduction)
    (B : HerglotzPositivity) :
    StieltjesPositiveSpectral :=
  R.from_herglotz B

def stieltjes_to_herglotz_reduction
    (R : HerglotzStieltjesReduction)
    (C : StieltjesPositiveSpectral) :
    HerglotzPositivity :=
  R.from_stieltjes_to_herglotz C

theorem herglotz_stieltjes_interderivable
    (R : HerglotzStieltjesReduction) :
    (Nonempty HerglotzPositivity -> Nonempty StieltjesPositiveSpectral) ∧
      (Nonempty StieltjesPositiveSpectral -> Nonempty HerglotzPositivity) := by
  constructor
  · intro hB
    cases hB with
    | intro B =>
        exact ⟨R.from_herglotz B⟩
  · intro hC
    cases hC with
    | intro C =>
        exact ⟨R.from_stieltjes_to_herglotz C⟩

theorem herglotz_stieltjes_nonempty_iff
    (R : HerglotzStieltjesReduction) :
    Iff (Nonempty HerglotzPositivity) (Nonempty StieltjesPositiveSpectral) := by
  have BC := herglotz_stieltjes_interderivable R
  exact Iff.intro BC.left BC.right

inductive GombocEquivalenceScope where
  | standardPositivityInterderivability
  | completedXiReadbackHardBoundary
  | rhConclusionRequiresXiCertificate

def canonicalGombocEquivalenceScope :
    List GombocEquivalenceScope :=
  [ GombocEquivalenceScope.standardPositivityInterderivability,
    GombocEquivalenceScope.completedXiReadbackHardBoundary,
    GombocEquivalenceScope.rhConclusionRequiresXiCertificate ]

structure GombocEquivalence where
  pick_herglotz : PickHerglotzReduction
  herglotz_stieltjes : HerglotzStieltjesReduction
  scope_markers : List GombocEquivalenceScope
  scope_markers_scope :
    scope_markers = canonicalGombocEquivalenceScope

theorem gomboc_equivalence_scope_count
    (E : GombocEquivalence) :
    E.scope_markers.length = 3 := by
  rw [E.scope_markers_scope]
  rfl

def gomboc_equivalence_bridge
    (E : GombocEquivalence) :
    AnalyticGombocEquivalenceBridge :=
  { hard_boundaries := canonicalAnalyticGombocHardBoundaries
    hard_boundaries_scope := rfl
    A_to_B := E.pick_herglotz.from_pick
    B_to_C := E.herglotz_stieltjes.from_herglotz
    C_to_A := fun C =>
      E.pick_herglotz.from_herglotz_to_pick
        (E.herglotz_stieltjes.from_stieltjes_to_herglotz C) }

theorem gomboc_A_B_C_interderivable
    (E : GombocEquivalence) :
    (Nonempty PickHilbertDecomposition -> Nonempty HerglotzPositivity) ∧
      (Nonempty HerglotzPositivity -> Nonempty PickHilbertDecomposition) ∧
        (Nonempty HerglotzPositivity -> Nonempty StieltjesPositiveSpectral) ∧
          (Nonempty StieltjesPositiveSpectral -> Nonempty HerglotzPositivity) := by
  have AB := pick_herglotz_interderivable E.pick_herglotz
  have BC := herglotz_stieltjes_interderivable E.herglotz_stieltjes
  exact ⟨AB.left, AB.right, BC.left, BC.right⟩

theorem gomboc_A_B_C_nonempty_iff
    (E : GombocEquivalence) :
    (Iff (Nonempty PickHilbertDecomposition) (Nonempty HerglotzPositivity)) ∧
      (Iff (Nonempty HerglotzPositivity) (Nonempty StieltjesPositiveSpectral)) := by
  exact
    ⟨pick_herglotz_nonempty_iff E.pick_herglotz,
      herglotz_stieltjes_nonempty_iff E.herglotz_stieltjes⟩

structure GombocFormsWithRH where
  pick_A : PickHilbertDecomposition
  herglotz_B : HerglotzPositivity
  stieltjes_C : StieltjesPositiveSpectral
  constructive_rh : ConstructiveRH

def gomboc_forms_with_rh_from_pick
    (E : GombocEquivalence)
    (A : PickHilbertDecomposition) :
    GombocFormsWithRH :=
  let B := E.pick_herglotz.from_pick A
  { pick_A := A
    herglotz_B := B
    stieltjes_C := E.herglotz_stieltjes.from_herglotz B
    constructive_rh := rh_from_pick_hilbert_decomposition A }

theorem gomboc_equivalence_from_pick_reaches_all
    (E : GombocEquivalence)
    (A : PickHilbertDecomposition) :
    Nonempty HerglotzPositivity ∧
      Nonempty StieltjesPositiveSpectral ∧ ConstructiveRH := by
  let B := E.pick_herglotz.from_pick A
  exact ⟨⟨B⟩, ⟨E.herglotz_stieltjes.from_herglotz B⟩,
    rh_from_pick_hilbert_decomposition A⟩

theorem analytic_gomboc_hard_boundary_count :
    canonicalAnalyticGombocHardBoundaries.length = 5 := by
  rfl

def A_to_B_to_C_to_A
    (bridge : AnalyticGombocEquivalenceBridge)
    (A : PickHilbertDecomposition) :
    PickHilbertDecomposition :=
  bridge.C_to_A (bridge.B_to_C (bridge.A_to_B A))

inductive ExcludedGombocRoute where
  | localZeroSideContainer
  | hiddenExponentialScaleBallast
  | termwiseSearch

def canonicalExcludedGombocRoutes : List ExcludedGombocRoute :=
  [ ExcludedGombocRoute.localZeroSideContainer,
    ExcludedGombocRoute.hiddenExponentialScaleBallast,
    ExcludedGombocRoute.termwiseSearch ]

structure ExponentialScaleResidualLedger where
  residual : Rat
  residual_zero : RatEq residual ratZero
  ledger_channel : Nat

structure NoHiddenBallast where
  prime_tower : PrimeCausalTower
  forward_from_primes_obligations :
    List PrimeTowerFrontierObligation
  forward_from_primes_scope :
    forward_from_primes_obligations =
      canonicalPrimeTowerFrontierObligations
  exponential_scale_residual : ExponentialScaleResidualLedger
  no_positive_scale_residual :
    forall r : Rat,
      ratLt ratZero r ->
        RatEq r exponential_scale_residual.residual ->
          False
  excluded_routes : List ExcludedGombocRoute
  excluded_routes_scope :
    excluded_routes = canonicalExcludedGombocRoutes

theorem excluded_gomboc_route_count :
    canonicalExcludedGombocRoutes.length = 3 := by
  rfl

theorem no_hidden_ballast_forward_obligation_count
    (N : NoHiddenBallast) :
    N.forward_from_primes_obligations.length = 4 := by
  rw [N.forward_from_primes_scope]
  rfl

theorem no_hidden_ballast_excluded_route_count
    (N : NoHiddenBallast) :
    N.excluded_routes.length = 3 := by
  rw [N.excluded_routes_scope]
  rfl

structure AnalyticGombocRHHandoff where
  hard_boundaries : List AnalyticGombocHardBoundary
  hard_boundaries_scope :
    hard_boundaries = canonicalAnalyticGombocHardBoundaries
  rh_from_herglotz :
    HerglotzPositivity -> ConstructiveRH
  rh_from_stieltjes :
    StieltjesPositiveSpectral -> ConstructiveRH

theorem rh_via_herglotz_positivity
    (handoff : AnalyticGombocRHHandoff)
    (B : HerglotzPositivity) :
    ConstructiveRH := by
  intro s zero
  exact handoff.rh_from_herglotz B s zero

theorem rh_via_stieltjes_positive_spectral
    (handoff : AnalyticGombocRHHandoff)
    (C : StieltjesPositiveSpectral) :
    ConstructiveRH := by
  intro s zero
  exact handoff.rh_from_stieltjes C s zero

def gomboc_forms_with_rh_from_herglotz
    (E : GombocEquivalence)
    (handoff : AnalyticGombocRHHandoff)
    (B : HerglotzPositivity) :
    GombocFormsWithRH :=
  { pick_A := E.pick_herglotz.from_herglotz_to_pick B
    herglotz_B := B
    stieltjes_C := E.herglotz_stieltjes.from_herglotz B
    constructive_rh := handoff.rh_from_herglotz B }

def gomboc_forms_with_rh_from_stieltjes
    (E : GombocEquivalence)
    (handoff : AnalyticGombocRHHandoff)
    (C : StieltjesPositiveSpectral) :
    GombocFormsWithRH :=
  let B := E.herglotz_stieltjes.from_stieltjes_to_herglotz C
  { pick_A := E.pick_herglotz.from_herglotz_to_pick B
    herglotz_B := B
    stieltjes_C := C
    constructive_rh := handoff.rh_from_stieltjes C }

theorem gomboc_equivalence_from_herglotz_reaches_all
    (E : GombocEquivalence)
    (handoff : AnalyticGombocRHHandoff)
    (B : HerglotzPositivity) :
    Nonempty PickHilbertDecomposition ∧
      Nonempty StieltjesPositiveSpectral ∧ ConstructiveRH := by
  exact
    ⟨⟨E.pick_herglotz.from_herglotz_to_pick B⟩,
      ⟨E.herglotz_stieltjes.from_herglotz B⟩,
      handoff.rh_from_herglotz B⟩

theorem gomboc_equivalence_from_stieltjes_reaches_all
    (E : GombocEquivalence)
    (handoff : AnalyticGombocRHHandoff)
    (C : StieltjesPositiveSpectral) :
    Nonempty PickHilbertDecomposition ∧
      Nonempty HerglotzPositivity ∧ ConstructiveRH := by
  let B := E.herglotz_stieltjes.from_stieltjes_to_herglotz C
  exact
    ⟨⟨E.pick_herglotz.from_herglotz_to_pick B⟩, ⟨B⟩,
      handoff.rh_from_stieltjes C⟩

structure AnalyticGombocForXi where
  pick_hilbert_A : PickHilbertDecomposition
  herglotz_B : HerglotzPositivity
  stieltjes_C : StieltjesPositiveSpectral
  equivalence_bridge : AnalyticGombocEquivalenceBridge
  gomboc_equivalence : GombocEquivalence
  equivalence_bridge_scope :
    equivalence_bridge = gomboc_equivalence_bridge gomboc_equivalence
  rh_handoff : AnalyticGombocRHHandoff
  no_hidden_ballast : NoHiddenBallast

theorem analytic_gomboc_for_xi_bridge_reads_gomboc_equivalence
    (G : AnalyticGombocForXi) :
    G.equivalence_bridge = gomboc_equivalence_bridge G.gomboc_equivalence := by
  exact G.equivalence_bridge_scope

def analytic_gomboc_for_xi_forms_from_pick
    (G : AnalyticGombocForXi)
    (A : PickHilbertDecomposition) :
    GombocFormsWithRH :=
  gomboc_forms_with_rh_from_pick G.gomboc_equivalence A

def analytic_gomboc_for_xi_forms_from_herglotz
    (G : AnalyticGombocForXi)
    (B : HerglotzPositivity) :
    GombocFormsWithRH :=
  gomboc_forms_with_rh_from_herglotz G.gomboc_equivalence G.rh_handoff B

def analytic_gomboc_for_xi_forms_from_stieltjes
    (G : AnalyticGombocForXi)
    (C : StieltjesPositiveSpectral) :
    GombocFormsWithRH :=
  gomboc_forms_with_rh_from_stieltjes G.gomboc_equivalence G.rh_handoff C

theorem rh_via_analytic_gomboc_from_pick
    (G : AnalyticGombocForXi) :
    ConstructiveRH := by
  exact rh_from_pick_hilbert_decomposition G.pick_hilbert_A

theorem rh_via_analytic_gomboc_from_herglotz
    (G : AnalyticGombocForXi) :
    ConstructiveRH := by
  intro s zero
  exact G.rh_handoff.rh_from_herglotz G.herglotz_B s zero

theorem rh_via_analytic_gomboc_from_stieltjes
    (G : AnalyticGombocForXi) :
    ConstructiveRH := by
  intro s zero
  exact G.rh_handoff.rh_from_stieltjes G.stieltjes_C s zero

theorem rh_via_analytic_gomboc
    (G : AnalyticGombocForXi) :
    ConstructiveRH := by
  exact rh_via_analytic_gomboc_from_pick G

structure ToyPickPositivityA where
  kernel_quadratic : KernelGramPacket -> Rat
  kernel_quadratic_nonnegative :
    forall packet : KernelGramPacket,
      ratLe ratZero (kernel_quadratic packet)

structure ToyHerglotzPositivityB where
  real_part : RatComplex -> Rat
  real_part_nonnegative :
    forall z : RatComplex, ratLe ratZero (real_part z)

structure ToyStieltjesPositiveSpectralC where
  Atom : Type
  mass : Atom -> Rat
  kernel : Rat -> Atom -> Rat
  integral : Rat -> Rat
  mass_nonnegative : forall a : Atom, ratLe ratZero (mass a)
  kernel_nonnegative :
    forall x : Rat, ratLe ratZero x ->
      forall a : Atom, ratLe ratZero (kernel x a)
  integral_nonnegative :
    forall x : Rat, ratLe ratZero x -> ratLe ratZero (integral x)

def toyPickA_constant_one : ToyPickPositivityA :=
  { kernel_quadratic := fun _ => ratOne
    kernel_quadratic_nonnegative := fun _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg }

def toyHerglotzB_constant_one : ToyHerglotzPositivityB :=
  { real_part := fun _ => ratOne
    real_part_nonnegative := fun _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg }

def toyStieltjesC_single_atom : ToyStieltjesPositiveSpectralC :=
  { Atom := Unit
    mass := fun _ => ratOne
    kernel := fun _ _ => ratOne
    integral := fun _ => ratOne
    mass_nonnegative := fun _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    kernel_nonnegative := fun _ _ _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    integral_nonnegative := fun _ _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg }

def toyHerglotzPositivity_constant_one : HerglotzPositivity :=
  { xi_log_derivative_real_part := fun _ => ratOne
    source_side_readback_obligations := canonicalHerglotzReadbackObligations
    source_side_readback_scope := rfl
    no_illegal_scale_source_sink := fun _ _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    right_half_plane_scope := fun _ _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg }

def toyLocatedPositiveSpectralMeasure_single_atom :
    LocatedPositiveSpectralMeasure :=
  { Atom := Unit
    mass := fun _ => ratOne
    spectral_location := fun _ => ratZero
    mass_nonnegative := fun _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    location_nonnegative := fun _ => ratLe_refl ratZero
    cauchy_kernel := fun _ _ => ratOne
    kernel_nonnegative := fun _ _ _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    integral := fun _ => ratOne
    integral_nonnegative := fun _ _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    readback_obligations := canonicalStieltjesReadbackObligations
    readback_obligations_scope := rfl }

def toyStieltjesPositiveSpectral_single_atom :
    StieltjesPositiveSpectral :=
  { spectral_measure := toyLocatedPositiveSpectralMeasure_single_atom
    dlog_xi_half_sqrt := fun _ => ratOne
    stieltjes_readback := fun _ _ => RatEq_refl ratOne
    positive_spectral_measure := fun _ =>
      BEDC.Real.RatNumLogEnclosure.ratOne_nonneg }

theorem toy_gomboc_positivity_witnesses_inhabited :
    Nonempty ToyPickPositivityA ∧
      Nonempty ToyHerglotzPositivityB ∧
        Nonempty ToyStieltjesPositiveSpectralC := by
  exact ⟨⟨toyPickA_constant_one⟩, ⟨toyHerglotzB_constant_one⟩,
    ⟨toyStieltjesC_single_atom⟩⟩

theorem toy_B_C_certificates_inhabited :
    Nonempty HerglotzPositivity ∧ Nonempty StieltjesPositiveSpectral := by
  exact ⟨⟨toyHerglotzPositivity_constant_one⟩,
    ⟨toyStieltjesPositiveSpectral_single_atom⟩⟩

theorem toy_pick_A_sample_positive
    (packet : KernelGramPacket) :
    ratLe ratZero (toyPickA_constant_one.kernel_quadratic packet) := by
  exact toyPickA_constant_one.kernel_quadratic_nonnegative packet

theorem toy_herglotz_B_sample_positive
    (z : RatComplex) :
    ratLe ratZero (toyHerglotzB_constant_one.real_part z) := by
  exact toyHerglotzB_constant_one.real_part_nonnegative z

theorem toy_stieltjes_C_sample_positive
    (x : Rat)
    (hx : ratLe ratZero x) :
    ratLe ratZero (toyStieltjesC_single_atom.integral x) := by
  exact toyStieltjesC_single_atom.integral_nonnegative x hx

end BEDC.Derived.RHRoute.AnalyticGombocForXi
