import BEDC.Derived.RHRoute.FarEndUnityNormalization
import BEDC.Derived.RHRoute.PrimePhaseRadialReadback

namespace BEDC.Derived.RHRoute.AllPrimePhaseClosure

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.PrimePhaseRadialReadback

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev PrimePhaseSample :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseSample
abbrev PrimePhaseRadialStructure :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseRadialStructure
abbrev PrimePhaseRadialReadback :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseRadialReadback
abbrev PrimeWindowNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowNormalization

/--
有限素窗口上的全相位闭包面。`covers_window` 明确每个窗口素数都有一个
径向相位样本, 因而这里读到的是有限窗口的全部素坐标, 不是无限对象。
-/
structure FiniteAllPrimePhaseClosureSurface where
  window : PrimeWindow
  radial : PrimePhaseRadialStructure
  radial_window_eq : radial.channel.window.elems = window.elems
  covers_window :
    (p : Nat) -> window.mem p ->
      ∃ sample : PrimePhaseSample, sample ∈ radial.samples ∧ sample.prime = p

structure FiniteAllPrimePhaseClosure
    (surface : FiniteAllPrimePhaseClosureSurface) where
  readback : PrimePhaseRadialReadback
  readback_surface : readback.surface = surface.radial

def closureFromSurface (surface : FiniteAllPrimePhaseClosureSurface) :
    FiniteAllPrimePhaseClosure surface where
  readback := readbackFromSurface surface.radial
  readback_surface := rfl

def closureReadbackValue {surface : FiniteAllPrimePhaseClosureSurface}
    (closure : FiniteAllPrimePhaseClosure surface) : RatNum :=
  closure.readback.readback

theorem covered_sample_in_radial_window
    {surface : FiniteAllPrimePhaseClosureSurface} {p : Nat}
    (member : surface.window.mem p) :
    ∃ sample : PrimePhaseSample,
      sample ∈ surface.radial.samples ∧ sample.prime = p ∧
        surface.radial.channel.window.mem sample.prime := by
  cases surface.covers_window p member with
  | intro sample sampleData =>
      exact
        ⟨sample, sampleData.left, sampleData.right,
          surface.radial.sample_mem_window sample sampleData.left⟩

theorem covered_prime_is_prime
    {surface : FiniteAllPrimePhaseClosureSurface} {p : Nat}
    (member : surface.window.mem p) :
    IsPrime p := by
  exact All.mem surface.window.all_prime member

theorem covered_sample_is_prime
    {surface : FiniteAllPrimePhaseClosureSurface} {p : Nat}
    (member : surface.window.mem p) :
    ∃ sample : PrimePhaseSample,
      sample ∈ surface.radial.samples ∧ sample.prime = p ∧
        IsPrime sample.prime := by
  cases covered_sample_in_radial_window (surface := surface) member with
  | intro sample sampleData =>
      exact
        ⟨sample, sampleData.left, sampleData.right.left,
          sample_prime sampleData.left⟩

theorem closure_readback_consistent
    {surface : FiniteAllPrimePhaseClosureSurface}
    (closure : FiniteAllPrimePhaseClosure surface) :
    RatEq (closureReadbackValue closure) (radialReadbackValue surface.radial) := by
  unfold closureReadbackValue
  rw [← closure.readback_surface]
  exact closure.readback.readback_eq

theorem closure_from_surface_consistent
    (surface : FiniteAllPrimePhaseClosureSurface) :
    RatEq (closureReadbackValue (closureFromSurface surface))
      (radialReadbackValue surface.radial) := by
  exact closure_readback_consistent (closureFromSurface surface)

theorem closure_readback_deterministic
    {surface : FiniteAllPrimePhaseClosureSurface}
    (left right : FiniteAllPrimePhaseClosure surface) :
    RatEq (closureReadbackValue left) (closureReadbackValue right) := by
  unfold closureReadbackValue
  exact readback_deterministic left.readback right.readback
    left.readback_surface right.readback_surface

theorem closure_sample_radius_located
    {surface : FiniteAllPrimePhaseClosureSurface} {sample : PrimePhaseSample}
    (member : sample ∈ surface.radial.samples) :
    ratLe ratZero sample.radius ∨ ratLe sample.radius ratZero := by
  exact sample_radius_located member

/--
窗口归一化只作为已经给出的单位范数行传递到闭包面; 它不构造远端点。
-/
structure NormalizedFiniteAllPrimePhaseClosureSurface where
  closureSurface : FiniteAllPrimePhaseClosureSurface
  normalization : PrimeWindowNormalization
  normalization_window_eq :
    normalization.sourceWindow.elems = closureSurface.window.elems
  normalized_channel_eq :
    normalization.normalizedChannel = closureSurface.radial.channel

theorem normalized_closure_unit_norm
    (surface : NormalizedFiniteAllPrimePhaseClosureSurface) :
    RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        surface.closureSurface.radial.channel)
      ratOne := by
  rw [← surface.normalized_channel_eq]
  exact surface.normalization.unit_norm_transfers

structure AllPrimePhaseClosureReadback where
  surfaceFor : PrimeWindow -> FiniteAllPrimePhaseClosureSurface
  readbackFor :
    (window : PrimeWindow) ->
      FiniteAllPrimePhaseClosure (surfaceFor window)
  window_exact :
    (window : PrimeWindow) ->
      (surfaceFor window).window.elems = window.elems

def allPrimePhaseClosureReadbackAt
    (profile : AllPrimePhaseClosureReadback) (window : PrimeWindow) :
    RatNum :=
  closureReadbackValue (profile.readbackFor window)

theorem all_prime_phase_closure_readback_consistent
    (profile : AllPrimePhaseClosureReadback) (window : PrimeWindow) :
    RatEq (allPrimePhaseClosureReadbackAt profile window)
      (radialReadbackValue (profile.surfaceFor window).radial) := by
  exact closure_readback_consistent (profile.readbackFor window)

theorem all_prime_phase_closure_window_exact
    (profile : AllPrimePhaseClosureReadback) (window : PrimeWindow) :
    (profile.surfaceFor window).window.elems = window.elems := by
  exact profile.window_exact window

theorem all_prime_phase_closure_deterministic
    (profile : AllPrimePhaseClosureReadback) (window : PrimeWindow)
    (other : FiniteAllPrimePhaseClosure (profile.surfaceFor window)) :
    RatEq (allPrimePhaseClosureReadbackAt profile window)
      (closureReadbackValue other) := by
  exact closure_readback_deterministic (profile.readbackFor window) other

def singlePrimeClosureSurface : FiniteAllPrimePhaseClosureSurface where
  window := BEDC.Derived.RHRoute.UnitaryBalance.singlePrimeWindow
  radial := singlePrimePhaseRadialStructure
  radial_window_eq := rfl
  covers_window := by
    intro p member
    unfold PrimeWindow.mem BEDC.Derived.RHRoute.UnitaryBalance.singlePrimeWindow at member
    cases member with
    | head =>
        exact
          ⟨singlePrimePhaseSample, List.Mem.head [],
            rfl⟩
    | tail _ tailMember =>
        cases tailMember

def singlePrimeAllPhaseClosure :
    FiniteAllPrimePhaseClosure singlePrimeClosureSurface :=
  closureFromSurface singlePrimeClosureSurface

theorem singlePrimeAllPhaseClosure_consistent :
    RatEq (closureReadbackValue singlePrimeAllPhaseClosure)
      (radialReadbackValue singlePrimePhaseRadialStructure) := by
  exact closure_from_surface_consistent singlePrimeClosureSurface

theorem singlePrimeAllPhaseClosure_covers_two :
    ∃ sample : PrimePhaseSample,
      sample ∈ singlePrimeClosureSurface.radial.samples ∧
        sample.prime = 2 ∧ IsPrime sample.prime := by
  have member : singlePrimeClosureSurface.window.mem 2 := by
    unfold singlePrimeClosureSurface PrimeWindow.mem
      BEDC.Derived.RHRoute.UnitaryBalance.singlePrimeWindow
    exact List.Mem.head []
  exact covered_sample_is_prime (surface := singlePrimeClosureSurface) member

end BEDC.Derived.RHRoute.AllPrimePhaseClosure
