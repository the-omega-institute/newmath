import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.FunctionalEquationSymmetry
import BEDC.Derived.RHRoute.PrimeSkewDefect
import BEDC.Derived.RHRoute.UnitaryBalance

namespace BEDC.Derived.RHRoute.BoundaryTriadPrimeShadow

open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.FunctionalEquationSymmetry
open BEDC.Derived.RHRoute.PrimeSkewDefect
open BEDC.Derived.RHRoute.UnitaryBalance
open BEDC.Derived.RationalUp

abbrev RatComplex :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

abbrev SymmetryPoint :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.RationalComplex

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev PrimeLocalChannel :=
  BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel

abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface

def GeometricFixedSetBoundary : Prop :=
  ∀ z : SymmetryPoint, JFixed z ↔ CriticalLine z

def CertifiedZeroPredicate (s : RatComplex) : Prop :=
  BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated s

structure ExactZeroDecisionOperator where
  decide_zero : (s : RatComplex) -> Decidable (CertifiedZeroPredicate s)

def ExactZeroDecisionBoundary : Prop :=
  Nonempty ExactZeroDecisionOperator

def GlobalRigidityBoundary : Prop :=
  ConstructiveRH

structure BoundaryTriad where
  geometric_fixed_set : Prop
  exact_zero_decision : Prop
  global_zero_rigidity : Prop

def rhBoundaryTriad : BoundaryTriad where
  geometric_fixed_set := GeometricFixedSetBoundary
  exact_zero_decision := ExactZeroDecisionBoundary
  global_zero_rigidity := GlobalRigidityBoundary

theorem geometric_fixed_set_boundary_closed :
    GeometricFixedSetBoundary := by
  intro z
  exact criticalLine_J_fixed_iff z

theorem critical_line_is_J_fixed_readback (z : SymmetryPoint) :
    JFixed z ↔ CriticalLine z :=
  geometric_fixed_set_boundary_closed z

def exact_zero_decision_operator_classifies
    (D : ExactZeroDecisionOperator) (s : RatComplex) :
    Decidable (CertifiedZeroPredicate s) :=
  D.decide_zero s

theorem global_rigidity_consumes_certified_nontrivial_zero
    (R : GlobalRigidityBoundary) (s : RatComplex) :
    NontrivialZetaZero s -> OnCriticalLine s :=
  R s

theorem global_rigidity_reads_constructiveRH :
    GlobalRigidityBoundary = ConstructiveRH :=
  rfl

theorem rhBoundaryTriad_readback :
    rhBoundaryTriad.geometric_fixed_set = GeometricFixedSetBoundary ∧
      rhBoundaryTriad.exact_zero_decision = ExactZeroDecisionBoundary ∧
        rhBoundaryTriad.global_zero_rigidity = GlobalRigidityBoundary := by
  exact And.intro rfl (And.intro rfl rfl)

structure LPOOracle where
  decide_exists_true : (f : Nat -> Bool) -> Decidable (∃ n : Nat, f n = true)

def ExactZeroDecisionLPOHardObligation : Prop :=
  Nonempty (ExactZeroDecisionOperator -> LPOOracle)

inductive AxiomAuditReading : Type where
  | implementationFootprint
  | mathematicalNecessityLowerBound
  deriving DecidableEq

def printAxiomsReading : AxiomAuditReading :=
  AxiomAuditReading.implementationFootprint

theorem printAxiomsReading_not_mathematical_lower_bound :
    printAxiomsReading ≠
      AxiomAuditReading.mathematicalNecessityLowerBound := by
  intro h
  cases h

def SurfaceNormOne (surface : UnitaryBalanceSurface) : Prop :=
  RatEq (squaredNormOnWindow surface.channel) ratOne

theorem unitary_balance_surface_reads_norm_one
    (surface : UnitaryBalanceSurface) :
    SurfaceNormOne surface :=
  surface.norm_one

structure PrimeUnitaryFixedHalfChart where
  readout : RatComplex -> Prop
  to_critical_line : ∀ s : RatComplex, readout s -> OnCriticalLine s
  from_critical_line : ∀ s : RatComplex, OnCriticalLine s -> readout s

theorem prime_unitary_chart_is_fixed_half_readout
    (chart : PrimeUnitaryFixedHalfChart) (s : RatComplex) :
    chart.readout s ↔ OnCriticalLine s := by
  constructor
  · intro h
    exact chart.to_critical_line s h
  · intro h
    exact chart.from_critical_line s h

structure FinitePrimeImbalanceCert (s : RatComplex) where
  channels : MirrorPrimeChannels
  skew : PrimeSkewCertificate channels

namespace FinitePrimeImbalanceCert

def window {s : RatComplex} (cert : FinitePrimeImbalanceCert s) :
    PrimeWindow :=
  cert.channels.source.window

theorem selected_prime {s : RatComplex}
    (cert : FinitePrimeImbalanceCert s) :
    BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime cert.skew.prime := by
  exact
    BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewCertificate.source_prime
      cert.skew

theorem source_deviation_apart {s : RatComplex}
    (cert : FinitePrimeImbalanceCert s) :
    cert.channels.source.amp_num cert.skew.prime ≠
      Int.ofNat (cert.channels.source.amp_den cert.skew.prime) := by
  exact
    BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewCertificate.source_deviation_raw_apart
      cert.skew

end FinitePrimeImbalanceCert

structure EffectivePrimeTailBound
    (s : RatComplex) (cert : FinitePrimeImbalanceCert s) where
  budget : Nat

def OffLineZeroCert (s : RatComplex) : Prop :=
  NontrivialZetaZero s ∧ Not (OnCriticalLine s)

def PrimeShadowBridge : Prop :=
  ∀ s : RatComplex,
    OffLineZeroCert s ↔
      ∃ cert : FinitePrimeImbalanceCert s, Nonempty (EffectivePrimeTailBound s cert)

def PrimeShadowZeroIncompatibility : Prop :=
  ∀ (s : RatComplex) (_zero : NontrivialZetaZero s)
      (cert : FinitePrimeImbalanceCert s),
    Nonempty (EffectivePrimeTailBound s cert) -> False

def LocatedCriticalLineClassifier : Prop :=
  ∀ s : RatComplex, OnCriticalLine s ∨ Not (OnCriticalLine s)

theorem prime_shadow_bridge_excludes_off_line
    (bridge : PrimeShadowBridge)
    (incompatible : PrimeShadowZeroIncompatibility)
    {s : RatComplex}
    (off_line : OffLineZeroCert s) : False := by
  have shadow := (bridge s).mp off_line
  cases shadow with
  | intro cert tail =>
      exact incompatible s off_line.left cert tail

theorem constructiveRH_of_prime_shadow_bridge
    (bridge : PrimeShadowBridge)
    (incompatible : PrimeShadowZeroIncompatibility)
    (located : LocatedCriticalLineClassifier) :
    ConstructiveRH := by
  intro s zero
  cases located s with
  | inl on_line =>
      exact on_line
  | inr off_line =>
      exact False.elim
        (prime_shadow_bridge_excludes_off_line bridge incompatible
          (And.intro zero off_line))

theorem prime_shadow_bridge_reads_global_rigidity
    (bridge : PrimeShadowBridge)
    (incompatible : PrimeShadowZeroIncompatibility)
    (located : LocatedCriticalLineClassifier) :
    GlobalRigidityBoundary :=
  constructiveRH_of_prime_shadow_bridge bridge incompatible located

end BEDC.Derived.RHRoute.BoundaryTriadPrimeShadow
