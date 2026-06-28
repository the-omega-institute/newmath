import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.LocatedZetaZero
import BEDC.Derived.RHRoute.SpectralRigidityRoute
import BEDC.Derived.RHRoute.ZetaZeroLocated

namespace BEDC.Derived.RHRoute.RHRouteFormalBridge

open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.LocatedZetaZero
open BEDC.Derived.RHRoute.SpectralRigidityRoute
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

universe u v

namespace Boundary

-- 这些标签只记录路线作用域。`classicalRHBoundary` 是未内化的边界行,
-- 不能从本文件读成经典 RH 的 BEDC 证明。
inductive RHRouteBoundary : Type where
  | locatedRatComplexSurface
  | locatedStreamSurface
  | generatedZeroSurface
  | spectralRigiditySurface
  | classicalRHBoundary

end Boundary

abbrev RatComplex : Type :=
  ConstructiveRHStatement.RatComplex

structure LocatedConstructiveZero where
  point : RatComplex
  zero : NontrivialZetaZero point

def LocatedConstructiveZero.zetaBoxData
    (located : LocatedConstructiveZero) :
    PSigma (fun point : RatComplex =>
      BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated point) :=
  ⟨located.point, located.zero.left⟩

def LocatedConstructiveZero.stripData
    (located : LocatedConstructiveZero) :
    PSigma (fun point : RatComplex => InCriticalStrip point) :=
  ⟨located.point, located.zero.right.left⟩

def LocatedConstructiveZero.notTrivialData
    (located : LocatedConstructiveZero) :
    PSigma (fun point : RatComplex => Not (TrivialZero point)) :=
  ⟨located.point, located.zero.right.right.left⟩

def LocatedConstructiveZero.notPoleData
    (located : LocatedConstructiveZero) :
    PSigma (fun point : RatComplex =>
      Not (RatComplexEq point zetaPolePoint)) :=
  ⟨located.point, located.zero.right.right.right⟩

structure RHRouteFormalBridge
    (I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface) where
  spectral_route : SpectralRigidityRoute I
  epsilon :
    GeneratedZero spectral_route.signature ->
      SourceZeroPoint
  generated_closed :
    FixedHalfClosedZeroSignature epsilon
  located_zero : LocatedConstructiveZero
  located_stream : LocatedZetaZero
  boundary : Boundary.RHRouteBoundary

def RHRouteFormalBridge.locatedBoxData
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    PSigma (fun point : RatComplex =>
      BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated point) :=
  bridge.located_zero.zetaBoxData

def RHRouteFormalBridge.locatedStreamData
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    Sigma (fun loc : LocatedComplex =>
      forall n : Nat, ZetaRectIndexCert (loc.R n) 1) :=
  existsLocatedData bridge.located_stream

def RHRouteFormalBridge.generatedLineData
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    PSigma (fun z : GeneratedZero bridge.spectral_route.signature =>
      BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
        (bridge.epsilon z)) :=
  ⟨bridge.spectral_route.thread.generated,
    generatedFixedHalf_criticalLine bridge.generated_closed
      bridge.spectral_route.thread.generated⟩

def RHRouteFormalBridge.spectralConstructiveData
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    PSigma (fun _ : SpectralRigidityRoute I => ConstructiveRH) :=
  ⟨bridge.spectral_route,
    spectralRigidityRoute_reads_constructiveRH bridge.spectral_route⟩

structure RHRouteInterfaceConsistency
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) where
  located_box_zero :
    BEDC.Derived.RHRoute.ZetaZeroLocated.ZetaZeroLocated
      bridge.located_zero.point
  located_in_strip : InCriticalStrip bridge.located_zero.point
  located_not_trivial : Not (TrivialZero bridge.located_zero.point)
  located_not_pole :
    Not (RatComplexEq bridge.located_zero.point zetaPolePoint)
  constructive_line : OnCriticalLine bridge.located_zero.point
  functional_line : OnCriticalLineSymmetryReadback bridge.located_zero.point
  j_fixed_line : OnCriticalLineJFixedReadback bridge.located_zero.point
  generated_line :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
      (bridge.epsilon bridge.spectral_route.thread.generated)
  spectral_thread_readback :
    BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy.forgetToGeneratedZero
      bridge.spectral_route.thread.layer =
        bridge.spectral_route.thread.generated

theorem bridge_reads_constructiveRH
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    ConstructiveRH :=
  spectralRigidityRoute_reads_constructiveRH bridge.spectral_route

theorem bridge_located_zero_on_critical_line
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    OnCriticalLine bridge.located_zero.point := by
  exact (bridge_reads_constructiveRH bridge)
    bridge.located_zero.point bridge.located_zero.zero

theorem bridge_located_zero_functional_line
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    OnCriticalLineSymmetryReadback bridge.located_zero.point := by
  exact onCriticalLine_to_functionalSymmetry bridge.located_zero.point
    (bridge_located_zero_on_critical_line bridge)

theorem bridge_located_zero_j_fixed
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    OnCriticalLineJFixedReadback bridge.located_zero.point := by
  exact onCriticalLine_to_JFixed bridge.located_zero.point
    (bridge_located_zero_on_critical_line bridge)

theorem bridge_generated_line
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    BEDC.Derived.RHRoute.FunctionalEquationSymmetry.CriticalLine
      (bridge.epsilon bridge.spectral_route.thread.generated) :=
  generatedFixedHalf_criticalLine bridge.generated_closed
    bridge.spectral_route.thread.generated

theorem bridge_spectral_thread_readback
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy.forgetToGeneratedZero
      bridge.spectral_route.thread.layer =
        bridge.spectral_route.thread.generated :=
  spectralRigidityRoute_thread_readback bridge.spectral_route

def bridge_interface_consistency
    {I : BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewDefectInterface}
    (bridge : RHRouteFormalBridge I) :
    RHRouteInterfaceConsistency bridge :=
  { located_box_zero := bridge.located_zero.zero.left
    located_in_strip := bridge.located_zero.zero.right.left
    located_not_trivial := bridge.located_zero.zero.right.right.left
    located_not_pole := bridge.located_zero.zero.right.right.right
    constructive_line := bridge_located_zero_on_critical_line bridge
    functional_line := bridge_located_zero_functional_line bridge
    j_fixed_line := bridge_located_zero_j_fixed bridge
    generated_line := bridge_generated_line bridge
    spectral_thread_readback := bridge_spectral_thread_readback bridge }

end BEDC.Derived.RHRoute.RHRouteFormalBridge
