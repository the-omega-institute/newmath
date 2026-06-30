import BEDC.Derived.RHRoute.UnitaryBalance
import BEDC.Derived.RHRoute.ZetaBoxEvaluator
import BEDC.Derived.RHRoute.ZetaInheritedInvariants

namespace BEDC.Derived.RHRoute.PrimePhaseRadialReadback

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.UnitaryBalance
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RationalUp

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev PrimeLocalChannel := BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel
abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface
abbrev Rat := BEDC.Derived.RationalUp.RatNum
abbrev RatComplex := BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex
abbrev PrimeClockTransfer :=
  BEDC.Derived.RHRoute.ZetaInheritedInvariants.PrimeClockTransfer

structure PrimePhaseSample where
  prime : Nat
  phase : RatComplex
  radius : Rat

def phaseRadiusNorm (sample : PrimePhaseSample) : Rat :=
  ratComplexNormSq sample.phase

structure PrimePhaseRadialStructure where
  channel : PrimeLocalChannel
  clocks : PrimeClockTransfer
  clocks_window_eq : clocks.window.elems = channel.window.elems
  samples : List PrimePhaseSample
  sample_mem_window :
    (sample : PrimePhaseSample) -> sample ∈ samples ->
      channel.window.mem sample.prime
  sample_phase_norm :
    (sample : PrimePhaseSample) -> sample ∈ samples ->
      RatEq sample.radius (phaseRadiusNorm sample)
  sample_radius_located :
    (sample : PrimePhaseSample) -> sample ∈ samples ->
      ratLe ratZero sample.radius ∨ ratLe sample.radius ratZero

def sampleAmplitude
    (surface : PrimePhaseRadialStructure) (sample : PrimePhaseSample) : Rat :=
  channelAmplitude surface.channel sample.prime

def sampleClockReadback
    (surface : PrimePhaseRadialStructure) (sample : PrimePhaseSample) : Nat :=
  BEDC.Derived.RHRoute.ZetaInheritedInvariants.logPrimeClock
    surface.clocks sample.prime

def sampleAmplitudeRadialWeight
    (surface : PrimePhaseRadialStructure) (sample : PrimePhaseSample) : Rat :=
  ratMul (sampleAmplitude surface sample) sample.radius

def radialWeightList
    (surface : PrimePhaseRadialStructure) : List Rat :=
  List.map (sampleAmplitudeRadialWeight surface) surface.samples

def radialWeightSum : List Rat -> Rat
  | [] => ratZero
  | weight :: weights => ratAdd weight (radialWeightSum weights)

def radialReadbackValue (surface : PrimePhaseRadialStructure) : Rat :=
  radialWeightSum (radialWeightList surface)

structure PrimePhaseRadialReadback where
  surface : PrimePhaseRadialStructure
  readback : Rat
  readback_eq : RatEq readback (radialReadbackValue surface)

def readbackFromSurface
    (surface : PrimePhaseRadialStructure) : PrimePhaseRadialReadback where
  surface := surface
  readback := radialReadbackValue surface
  readback_eq := RatEq_refl _

structure BalancedPrimePhaseRadialReadback where
  balance : UnitaryBalanceSurface
  readback : PrimePhaseRadialReadback
  same_channel : readback.surface.channel = balance.channel

theorem sample_prime
    {surface : PrimePhaseRadialStructure} {sample : PrimePhaseSample}
    (member : sample ∈ surface.samples) :
    IsPrime sample.prime := by
  exact All.mem surface.channel.window.all_prime
    (surface.sample_mem_window sample member)

theorem sample_radius_is_phase_norm
    {surface : PrimePhaseRadialStructure} {sample : PrimePhaseSample}
    (member : sample ∈ surface.samples) :
    RatEq sample.radius (phaseRadiusNorm sample) := by
  exact surface.sample_phase_norm sample member

theorem sample_radius_located
    {surface : PrimePhaseRadialStructure} {sample : PrimePhaseSample}
    (member : sample ∈ surface.samples) :
    ratLe ratZero sample.radius ∨ ratLe sample.radius ratZero := by
  exact surface.sample_radius_located sample member

theorem sample_mem_clock_window
    {surface : PrimePhaseRadialStructure} {sample : PrimePhaseSample}
    (member : sample ∈ surface.samples) :
    surface.clocks.window.mem sample.prime := by
  unfold PrimeWindow.mem
  rw [surface.clocks_window_eq]
  exact surface.sample_mem_window sample member

theorem sample_clock_matches_frequency
    (surface : PrimePhaseRadialStructure) (sample : PrimePhaseSample) :
    sampleClockReadback surface sample =
      surface.clocks.fourierFrequency sample.prime := by
  rfl

theorem sample_clock_source_prime
    {surface : PrimePhaseRadialStructure} {sample : PrimePhaseSample}
    (member : sample ∈ surface.samples) :
    IsPrime sample.prime := by
  exact
    BEDC.Derived.RHRoute.ZetaInheritedInvariants.logPrimeClock_source_is_prime
      surface.clocks sample.prime (sample_mem_clock_window member)

theorem readbackFromSurface_exact
    (surface : PrimePhaseRadialStructure) :
    RatEq (readbackFromSurface surface).readback
      (radialReadbackValue surface) := by
  exact RatEq_refl _

theorem readback_deterministic
    {surface : PrimePhaseRadialStructure}
    (left right : PrimePhaseRadialReadback)
    (left_surface : left.surface = surface)
    (right_surface : right.surface = surface) :
    RatEq left.readback right.readback := by
  have left_eq : RatEq left.readback (radialReadbackValue surface) := by
    cases left_surface
    exact left.readback_eq
  have right_eq : RatEq right.readback (radialReadbackValue surface) := by
    cases right_surface
    exact right.readback_eq
  exact RatEq_trans left.readback (radialReadbackValue surface) right.readback
    left_eq (RatEq_symm right_eq)

theorem balanced_readback_channel_supported
    (balanced : BalancedPrimePhaseRadialReadback) (p : Nat) :
    Not (balanced.balance.channel.window.mem p) ->
      balanced.readback.surface.channel.amp_num p = 0 := by
  intro outside
  rw [balanced.same_channel]
  exact balanced.balance.channel.supported p outside

theorem balanced_readback_norm_one
    (balanced : BalancedPrimePhaseRadialReadback) :
    RatEq (squaredNormOnWindow balanced.readback.surface.channel) ratOne := by
  rw [balanced.same_channel]
  exact balanced.balance.norm_one

theorem balanced_readback_clock_window_matches_channel
    (balanced : BalancedPrimePhaseRadialReadback) :
    balanced.readback.surface.clocks.window.elems =
      balanced.balance.channel.window.elems := by
  rw [← balanced.same_channel]
  exact balanced.readback.surface.clocks_window_eq

def singlePrimePhaseSample : PrimePhaseSample where
  prime := 2
  phase := ratComplexOne
  radius := ratOne

def singlePrimeClockTransfer : PrimeClockTransfer where
  window := singlePrimeWindow
  fourierFrequency := fun p => if p = 2 then 1 else 0

def singlePrimePhaseRadialStructure : PrimePhaseRadialStructure where
  channel := singlePrimeChannel
  clocks := singlePrimeClockTransfer
  clocks_window_eq := rfl
  samples := [singlePrimePhaseSample]
  sample_mem_window := by
    intro sample member
    cases member with
    | head =>
        exact List.Mem.head []
    | tail _ tailMember =>
        cases tailMember
  sample_phase_norm := by
    intro sample member
    cases member with
    | head =>
        exact RatEq_refl _
    | tail _ tailMember =>
        cases tailMember
  sample_radius_located := by
    intro sample member
    cases member with
    | head =>
        exact ratLe_total ratZero ratOne
    | tail _ tailMember =>
        cases tailMember

def singlePrimePhaseRadialReadback : PrimePhaseRadialReadback :=
  readbackFromSurface singlePrimePhaseRadialStructure

def singlePrimeBalancedPhaseRadialReadback :
    BalancedPrimePhaseRadialReadback where
  balance := singlePrimeUnitaryBalanceSurface
  readback := singlePrimePhaseRadialReadback
  same_channel := rfl

theorem singlePrimePhaseRadialReadback_exact :
    RatEq singlePrimePhaseRadialReadback.readback
      (radialReadbackValue singlePrimePhaseRadialStructure) := by
  exact readbackFromSurface_exact singlePrimePhaseRadialStructure

theorem singlePrimeBalancedPhaseRadialReadback_norm_one :
    RatEq
      (squaredNormOnWindow
        singlePrimeBalancedPhaseRadialReadback.readback.surface.channel)
      ratOne := by
  exact balanced_readback_norm_one singlePrimeBalancedPhaseRadialReadback

theorem singlePrimeClockReadback_exact :
    sampleClockReadback singlePrimePhaseRadialStructure
      singlePrimePhaseSample = 1 := by
  rfl

end BEDC.Derived.RHRoute.PrimePhaseRadialReadback
