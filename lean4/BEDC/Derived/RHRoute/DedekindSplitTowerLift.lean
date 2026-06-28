import BEDC.Derived.DedekindSumUp
import BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower
import BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy

namespace BEDC.Derived.RHRoute.DedekindSplitTowerLift

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.DedekindSumUp
open BEDC.Derived.RationalUp

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev IsPrime :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime

abbrev FinitePhaseEnergyLayer :=
  BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower.FinitePhaseEnergyLayer

abbrev WindowIncluded :=
  BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower.WindowIncluded

abbrev FinitePhaseEnergyTower :=
  BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower.FinitePhaseEnergyTower

abbrev PhaseEnergyExtensionStep :=
  BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower.PhaseEnergyExtensionStep

abbrev FinitePrimeTower :=
  BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower.FinitePrimeTower

abbrev FinitePrimeTowerPhaseReadoutFor :=
  BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower.FinitePhaseEnergyTower.FinitePrimeTowerPhaseReadoutFor

/--
Dedekind 分裂读数只记录一对正分母和对应的有限 Dedekind 和。
这里没有 reciprocity 定理、模群作用或解析 η 函数。
-/
structure DedekindSplitReadout where
  left : PositiveNat
  right : PositiveNat
  forward : RatNum
  backward : RatNum
  forward_eq_sum : RatEq forward (dedekindSum left right)
  backward_eq_sum : RatEq backward (dedekindSum right left)

namespace DedekindSplitReadout

def fromPositive (left right : PositiveNat) : DedekindSplitReadout where
  left := left
  right := right
  forward := dedekindSum left right
  backward := dedekindSum right left
  forward_eq_sum := RatEq_refl (dedekindSum left right)
  backward_eq_sum := RatEq_refl (dedekindSum right left)

theorem forward_sound (readout : DedekindSplitReadout) :
    RatEq readout.forward (dedekindSum readout.left readout.right) :=
  readout.forward_eq_sum

theorem backward_sound (readout : DedekindSplitReadout) :
    RatEq readout.backward (dedekindSum readout.right readout.left) :=
  readout.backward_eq_sum

end DedekindSplitReadout

/--
一层分裂塔 lift 的有限状态。`stage` 是 fuel 层号；`phase` 是有限
相位能量层；`spectral` 是递归谱零层；`readout` 是 Dedekind 和读数。
该结构不包含无限极限、全素数窗口或 RH 结论。
-/
structure DedekindSplitLayer (signature : RHFreeZeroSignature) where
  stage : Nat
  phase : FinitePhaseEnergyLayer
  spectral : SpectralZeroLayer signature
  readout : DedekindSplitReadout
  phase_energy_ok : phase.energy ≤ phase.bound
  spectral_depth_ok : layerDepth spectral = stage

namespace DedekindSplitLayer

def fromGeneratedZero {signature : RHFreeZeroSignature}
    (phase : FinitePhaseEnergyLayer)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    DedekindSplitLayer signature where
  stage := 0
  phase := phase
  spectral := SpectralZeroLayer.base z
  readout := readout
  phase_energy_ok := phase.energy_le_bound
  spectral_depth_ok := rfl

def fromFinitePhaseTower {signature : RHFreeZeroSignature}
    (tower : FinitePhaseEnergyTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    DedekindSplitLayer signature :=
  fromGeneratedZero tower.terminalLayer z readout

def fromTowerReadback {signature : RHFreeZeroSignature}
    (phase : FinitePhaseEnergyLayer)
    (fuel : Nat)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    DedekindSplitLayer signature where
  stage := fuel
  phase := phase
  spectral := towerReadbackLayer fuel z
  readout := readout
  phase_energy_ok := phase.energy_le_bound
  spectral_depth_ok := towerReadbackLayer_depth fuel z

def generatedZero {signature : RHFreeZeroSignature}
    (layer : DedekindSplitLayer signature) :
    GeneratedZero signature :=
  forgetToGeneratedZero layer.spectral

def energy (layer : DedekindSplitLayer signature) : Nat :=
  layer.phase.energy

def bound (layer : DedekindSplitLayer signature) : Nat :=
  layer.phase.bound

def window (layer : DedekindSplitLayer signature) : PrimeWindow :=
  layer.phase.window

theorem energy_bounded {signature : RHFreeZeroSignature}
    (layer : DedekindSplitLayer signature) :
    layer.energy ≤ layer.bound :=
  layer.phase_energy_ok

theorem depth_eq_stage {signature : RHFreeZeroSignature}
    (layer : DedekindSplitLayer signature) :
    layerDepth layer.spectral = layer.stage :=
  layer.spectral_depth_ok

theorem window_member_prime {signature : RHFreeZeroSignature}
    (layer : DedekindSplitLayer signature) {p : Nat} :
    PrimeWindow.mem p layer.window -> IsPrime p := by
  intro member
  exact layer.phase.window_member_prime member

theorem fromTowerReadback_depth {signature : RHFreeZeroSignature}
    (phase : FinitePhaseEnergyLayer)
    (fuel : Nat)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    layerDepth
        (fromTowerReadback phase fuel z readout).spectral =
      fuel := by
  exact towerReadbackLayer_depth fuel z

theorem fromTowerReadback_forget {signature : RHFreeZeroSignature}
    (phase : FinitePhaseEnergyLayer)
    (fuel : Nat)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    (fromTowerReadback phase fuel z readout).generatedZero =
      towerReadbackGenerated fuel z := by
  exact towerReadbackLayer_forget fuel z

end DedekindSplitLayer

/--
一层 lift 的闭合数据：相位层按已有有限扩展步骤前进，谱层只加一个
`recursiveTowerReadback` 事件，Dedekind 读数原样携带。
-/
structure DedekindSplitLiftStep {signature : RHFreeZeroSignature}
    (source target : DedekindSplitLayer signature) where
  event : TraceEvent
  phase_step : PhaseEnergyExtensionStep source.phase target.phase
  spectral_lift :
    target.spectral = SpectralZeroLayer.recursiveTowerReadback event source.spectral
  readout_preserved : target.readout = source.readout
  stage_lift : target.stage = Nat.succ source.stage

namespace DedekindSplitLiftStep

theorem energy_monotone {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    source.energy ≤ target.energy :=
  step.phase_step.energy_monotone

theorem target_energy_bounded {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    target.energy ≤ target.bound :=
  step.phase_step.target_energy_bounded

theorem window_included {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    WindowIncluded source.window target.window :=
  step.phase_step.window_included

theorem old_window_member {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target)
    {p : Nat} :
    PrimeWindow.mem p source.window -> PrimeWindow.mem p target.window := by
  intro member
  exact step.window_included p member

theorem target_depth_lift {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    layerDepth target.spectral = Nat.succ (layerDepth source.spectral) := by
  rw [step.spectral_lift]
  rfl

theorem generated_zero_lift {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    target.generatedZero =
      GeneratedZero.recursiveTowerReadback step.event source.generatedZero := by
  unfold DedekindSplitLayer.generatedZero
  rw [step.spectral_lift]
  rfl

theorem forward_readout_sound_after_lift {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    RatEq target.readout.forward
      (dedekindSum source.readout.left source.readout.right) := by
  rw [step.readout_preserved]
  exact source.readout.forward_sound

theorem backward_readout_sound_after_lift {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (step : DedekindSplitLiftStep source target) :
    RatEq target.readout.backward
      (dedekindSum source.readout.right source.readout.left) := by
  rw [step.readout_preserved]
  exact source.readout.backward_sound

end DedekindSplitLiftStep

def liftAlongPrime {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    DedekindSplitLayer signature where
  stage := Nat.succ source.stage
  phase := source.phase.extendPrime p prime
  spectral :=
    SpectralZeroLayer.recursiveTowerReadback
      (TraceEvent.refine source.stage (Nat.succ source.stage))
      source.spectral
  readout := source.readout
  phase_energy_ok := (source.phase.extendPrime p prime).energy_le_bound
  spectral_depth_ok := by
    change Nat.succ (layerDepth source.spectral) = Nat.succ source.stage
    exact congrArg Nat.succ source.spectral_depth_ok

def liftAlongPrimeStep {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    DedekindSplitLiftStep source (liftAlongPrime source p prime) where
  event := TraceEvent.refine source.stage (Nat.succ source.stage)
  phase_step := singlePrimeExtensionStep source.phase p prime
  spectral_lift := rfl
  readout_preserved := rfl
  stage_lift := rfl

theorem liftAlongPrime_energy_monotone {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    source.energy ≤ (liftAlongPrime source p prime).energy :=
  (liftAlongPrimeStep source p prime).energy_monotone

theorem liftAlongPrime_target_energy_bounded
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    (liftAlongPrime source p prime).energy ≤
      (liftAlongPrime source p prime).bound :=
  (liftAlongPrimeStep source p prime).target_energy_bounded

theorem liftAlongPrime_old_window_member
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p q : Nat)
    (prime : IsPrime p) :
    PrimeWindow.mem q source.window ->
      PrimeWindow.mem q (liftAlongPrime source p prime).window := by
  intro member
  exact (liftAlongPrimeStep source p prime).old_window_member member

theorem liftAlongPrime_new_window_member
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    PrimeWindow.mem p (liftAlongPrime source p prime).window := by
  exact source.phase.extendPrime_new_window p prime

theorem liftAlongPrime_depth
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    layerDepth (liftAlongPrime source p prime).spectral =
      Nat.succ source.stage := by
  exact (liftAlongPrime source p prime).spectral_depth_ok

theorem liftAlongPrime_generated_zero
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    (liftAlongPrime source p prime).generatedZero =
      GeneratedZero.recursiveTowerReadback
        (TraceEvent.refine source.stage (Nat.succ source.stage))
        source.generatedZero := by
  exact (liftAlongPrimeStep source p prime).generated_zero_lift

theorem liftAlongPrime_readout_preserved
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    (liftAlongPrime source p prime).readout = source.readout := by
  rfl

theorem liftAlongPrime_forward_readout_sound
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (p : Nat)
    (prime : IsPrime p) :
    RatEq (liftAlongPrime source p prime).readout.forward
      (dedekindSum
        (liftAlongPrime source p prime).readout.left
        (liftAlongPrime source p prime).readout.right) := by
  exact (liftAlongPrime source p prime).readout.forward_sound

inductive FiniteDedekindSplitLiftChain
    {signature : RHFreeZeroSignature} :
    DedekindSplitLayer signature -> DedekindSplitLayer signature -> Type 1 where
  | refl (layer : DedekindSplitLayer signature) :
      FiniteDedekindSplitLiftChain layer layer
  | step {source middle target : DedekindSplitLayer signature} :
      DedekindSplitLiftStep source middle ->
        FiniteDedekindSplitLiftChain middle target ->
          FiniteDedekindSplitLiftChain source target

namespace FiniteDedekindSplitLiftChain

def length {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature} :
    FiniteDedekindSplitLiftChain source target -> Nat
  | refl _ => 0
  | step _ rest => Nat.succ (length rest)

theorem terminal_energy_bounded
    {signature : RHFreeZeroSignature}
    {source target : DedekindSplitLayer signature}
    (chain : FiniteDedekindSplitLiftChain source target) :
    target.energy ≤ target.bound := by
  induction chain with
  | refl layer =>
      exact layer.energy_bounded
  | step _first _rest ih =>
      exact ih

theorem first_energy_le_next
    {signature : RHFreeZeroSignature}
    {source middle target : DedekindSplitLayer signature}
    (first : DedekindSplitLiftStep source middle)
    (_rest : FiniteDedekindSplitLiftChain middle target) :
    source.energy ≤ middle.energy :=
  first.energy_monotone

end FiniteDedekindSplitLiftChain

inductive PrimeLiftPlan : Type where
  | nil : PrimeLiftPlan
  | cons (p : Nat) (prime : IsPrime p) (rest : PrimeLiftPlan) :
      PrimeLiftPlan

namespace PrimeLiftPlan

def primes : PrimeLiftPlan -> List Nat
  | nil => []
  | cons p _ rest => p :: primes rest

def length : PrimeLiftPlan -> Nat
  | nil => 0
  | cons _ _ rest => Nat.succ (length rest)

def run {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature) :
    PrimeLiftPlan -> DedekindSplitLayer signature
  | nil => source
  | cons p prime rest =>
      run (liftAlongPrime source p prime) rest

theorem run_energy_bounded
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (plan : PrimeLiftPlan) :
    (run source plan).energy ≤ (run source plan).bound := by
  induction plan generalizing source with
  | nil =>
      exact source.energy_bounded
  | cons p prime rest ih =>
      exact ih (liftAlongPrime source p prime)

theorem run_readout_sound
    {signature : RHFreeZeroSignature}
    (source : DedekindSplitLayer signature)
    (plan : PrimeLiftPlan) :
    RatEq (run source plan).readout.forward
      (dedekindSum
        (run source plan).readout.left
        (run source plan).readout.right) := by
  exact (run source plan).readout.forward_sound

end PrimeLiftPlan

/--
从现有有限素数塔读出一个分裂层。该函数只使用 `FinitePrimeTower` 的
有限终端窗口和层数；无限 tower body 仍是论文侧 boundary。
-/
def fromFinitePrimeTowerReadout {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    DedekindSplitLayer signature :=
  DedekindSplitLayer.fromTowerReadback
    (FinitePhaseEnergyTower.fromFinitePrimeTower T).terminalLayer
    T.layerCount z readout

theorem fromFinitePrimeTowerReadout_stage
    {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    (fromFinitePrimeTowerReadout T z readout).stage = T.layerCount := by
  rfl

theorem fromFinitePrimeTowerReadout_energy
    {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    (fromFinitePrimeTowerReadout T z readout).energy = T.layerCount := by
  rfl

theorem fromFinitePrimeTowerReadout_energy_bounded
    {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    (fromFinitePrimeTowerReadout T z readout).energy ≤
      (fromFinitePrimeTowerReadout T z readout).bound := by
  exact (fromFinitePrimeTowerReadout T z readout).energy_bounded

theorem fromFinitePrimeTowerReadout_depth
    {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    layerDepth (fromFinitePrimeTowerReadout T z readout).spectral =
      T.layerCount := by
  exact towerReadbackLayer_depth T.layerCount z

theorem fromFinitePrimeTowerReadout_generated_zero
    {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    (fromFinitePrimeTowerReadout T z readout).generatedZero =
      towerReadbackGenerated T.layerCount z := by
  exact towerReadbackLayer_forget T.layerCount z

theorem fromFinitePrimeTowerReadout_forward_sound
    {signature : RHFreeZeroSignature}
    (T : FinitePrimeTower)
    (z : GeneratedZero signature)
    (readout : DedekindSplitReadout) :
    RatEq (fromFinitePrimeTowerReadout T z readout).readout.forward
      (dedekindSum
        (fromFinitePrimeTowerReadout T z readout).readout.left
        (fromFinitePrimeTowerReadout T z readout).readout.right) := by
  exact (fromFinitePrimeTowerReadout T z readout).readout.forward_sound

/--
边界谓词：该 Lean 文件登记的是有限层 lift，不登记无限相容极限、
全素数窗口、Dedekind η 完备化或 RH 证明。
-/
inductive InfiniteSplitTowerBoundary : Type where
  | infiniteCompatibleLimit
  | allPrimeWindow
  | dedekindEtaCompletion
  | rhDecisionRoute

def boundaryCode : InfiniteSplitTowerBoundary -> Nat
  | InfiniteSplitTowerBoundary.infiniteCompatibleLimit => 0
  | InfiniteSplitTowerBoundary.allPrimeWindow => 1
  | InfiniteSplitTowerBoundary.dedekindEtaCompletion => 2
  | InfiniteSplitTowerBoundary.rhDecisionRoute => 3

end BEDC.Derived.RHRoute.DedekindSplitTowerLift
