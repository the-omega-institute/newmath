import BEDC.Derived.RHRoute.FinitePrimeTowerReadout
import BEDC.Derived.RHRoute.RecursiveParityTower

namespace BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower

open BEDC.Derived.RHRoute.FinitePrimeWindow

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev IsPrime :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime

abbrev FinitePrimeTower :=
  BEDC.Derived.RHRoute.FinitePrimeTowerReadout.FinitePrimeTower

abbrev extendWindow :=
  BEDC.Derived.RHRoute.FinitePrimeTowerReadout.extendWindow

abbrev TowerParity :=
  BEDC.Derived.RHRoute.RecursiveParityTower.TowerParity

abbrev natParity :=
  BEDC.Derived.RHRoute.RecursiveParityTower.natParity

def WindowIncluded (small large : PrimeWindow) : Prop :=
  ∀ p : Nat, PrimeWindow.mem p small -> PrimeWindow.mem p large

structure FinitePhaseEnergyLayer where
  window : PrimeWindow
  -- 这里的 energy 是有限层计数账本, 不是解析或 Hamiltonian 能量。
  energy : Nat
  bound : Nat
  energy_bounded : energy ≤ bound

namespace FinitePhaseEnergyLayer

def fromWindow (window : PrimeWindow) : FinitePhaseEnergyLayer where
  window := window
  energy := 0
  bound := 0
  energy_bounded := Nat.le_refl 0

def extendPrime (layer : FinitePhaseEnergyLayer)
    (p : Nat) (prime : IsPrime p) : FinitePhaseEnergyLayer where
  window := extendWindow layer.window p prime
  energy := Nat.succ layer.energy
  bound := Nat.succ layer.bound
  energy_bounded := Nat.succ_le_succ layer.energy_bounded

def parity (layer : FinitePhaseEnergyLayer) : TowerParity :=
  natParity layer.energy

theorem energy_le_bound (layer : FinitePhaseEnergyLayer) :
    layer.energy ≤ layer.bound :=
  layer.energy_bounded

theorem extendPrime_energy (layer : FinitePhaseEnergyLayer)
    (p : Nat) (prime : IsPrime p) :
    (extendPrime layer p prime).energy = Nat.succ layer.energy := by
  rfl

theorem extendPrime_bound (layer : FinitePhaseEnergyLayer)
    (p : Nat) (prime : IsPrime p) :
    (extendPrime layer p prime).bound = Nat.succ layer.bound := by
  rfl

theorem extendPrime_energy_monotone (layer : FinitePhaseEnergyLayer)
    (p : Nat) (prime : IsPrime p) :
    layer.energy ≤ (extendPrime layer p prime).energy := by
  exact Nat.le_succ layer.energy

theorem extendPrime_old_window (layer : FinitePhaseEnergyLayer)
    (p q : Nat) (prime : IsPrime p) :
    PrimeWindow.mem q layer.window ->
      PrimeWindow.mem q (extendPrime layer p prime).window := by
  intro member
  exact
    BEDC.Derived.RHRoute.FinitePrimeTowerReadout.extendWindow_mem_old
      layer.window p q prime member

theorem extendPrime_new_window (layer : FinitePhaseEnergyLayer)
    (p : Nat) (prime : IsPrime p) :
    PrimeWindow.mem p (extendPrime layer p prime).window := by
  exact
    BEDC.Derived.RHRoute.FinitePrimeTowerReadout.extendWindow_mem_self
      layer.window p prime

theorem window_member_prime (layer : FinitePhaseEnergyLayer) {p : Nat} :
    PrimeWindow.mem p layer.window -> IsPrime p := by
  intro member
  exact All.mem layer.window.all_prime member

end FinitePhaseEnergyLayer

structure PhaseEnergyExtensionStep
    (source target : FinitePhaseEnergyLayer) where
  window_included : WindowIncluded source.window target.window
  energy_monotone : source.energy ≤ target.energy
  target_energy_bounded : target.energy ≤ target.bound

def singlePrimeExtensionStep (layer : FinitePhaseEnergyLayer)
    (p : Nat) (prime : IsPrime p) :
    PhaseEnergyExtensionStep layer (layer.extendPrime p prime) where
  window_included := by
    intro q member
    exact layer.extendPrime_old_window p q prime member
  energy_monotone := layer.extendPrime_energy_monotone p prime
  target_energy_bounded := (layer.extendPrime p prime).energy_le_bound

inductive AdjacentSteps : List FinitePhaseEnergyLayer -> Prop where
  | nil : AdjacentSteps []
  | single (layer : FinitePhaseEnergyLayer) : AdjacentSteps [layer]
  | cons (source target : FinitePhaseEnergyLayer)
      (rest : List FinitePhaseEnergyLayer) :
      PhaseEnergyExtensionStep target source ->
        AdjacentSteps (target :: rest) ->
          AdjacentSteps (source :: target :: rest)

structure FinitePhaseEnergyTower where
  terminal : FinitePhaseEnergyLayer
  history : List FinitePhaseEnergyLayer
  adjacent : AdjacentSteps (terminal :: history)

namespace FinitePhaseEnergyTower

def layers (tower : FinitePhaseEnergyTower) : List FinitePhaseEnergyLayer :=
  tower.terminal :: tower.history

def singleton (layer : FinitePhaseEnergyLayer) : FinitePhaseEnergyTower where
  terminal := layer
  history := []
  adjacent := AdjacentSteps.single layer

def fromPrimeWindow (window : PrimeWindow) : FinitePhaseEnergyTower :=
  singleton (FinitePhaseEnergyLayer.fromWindow window)

def terminalLayer (tower : FinitePhaseEnergyTower) :
    FinitePhaseEnergyLayer :=
  tower.terminal

def terminalWindow (tower : FinitePhaseEnergyTower) : PrimeWindow :=
  tower.terminalLayer.window

def terminalEnergy (tower : FinitePhaseEnergyTower) : Nat :=
  tower.terminalLayer.energy

def terminalBound (tower : FinitePhaseEnergyTower) : Nat :=
  tower.terminalLayer.bound

def terminalParity (tower : FinitePhaseEnergyTower) : TowerParity :=
  tower.terminalLayer.parity

def extendPrime (tower : FinitePhaseEnergyTower)
    (p : Nat) (prime : IsPrime p) : FinitePhaseEnergyTower where
  terminal := tower.terminalLayer.extendPrime p prime
  history := tower.terminalLayer :: tower.history
  adjacent :=
    AdjacentSteps.cons (tower.terminalLayer.extendPrime p prime)
      tower.terminalLayer tower.history
      (singlePrimeExtensionStep tower.terminalLayer p prime)
      tower.adjacent

theorem terminal_energy_bounded (tower : FinitePhaseEnergyTower) :
    tower.terminalEnergy ≤ tower.terminalBound := by
  unfold terminalEnergy terminalBound
  exact tower.terminalLayer.energy_le_bound

theorem extendPrime_terminal_energy (tower : FinitePhaseEnergyTower)
    (p : Nat) (prime : IsPrime p) :
    (tower.extendPrime p prime).terminalEnergy =
      Nat.succ tower.terminalEnergy := by
  rfl

theorem extendPrime_terminal_bound (tower : FinitePhaseEnergyTower)
    (p : Nat) (prime : IsPrime p) :
    (tower.extendPrime p prime).terminalBound =
      Nat.succ tower.terminalBound := by
  rfl

theorem extendPrime_terminal_energy_monotone
    (tower : FinitePhaseEnergyTower)
    (p : Nat) (prime : IsPrime p) :
    tower.terminalEnergy ≤ (tower.extendPrime p prime).terminalEnergy := by
  exact tower.terminalLayer.extendPrime_energy_monotone p prime

theorem extendPrime_terminal_window_included
    (tower : FinitePhaseEnergyTower)
    (p : Nat) (prime : IsPrime p) :
    WindowIncluded tower.terminalWindow
      (tower.extendPrime p prime).terminalWindow := by
  intro q member
  exact tower.terminalLayer.extendPrime_old_window p q prime member

theorem extendPrime_terminal_new_window
    (tower : FinitePhaseEnergyTower)
    (p : Nat) (prime : IsPrime p) :
    PrimeWindow.mem p (tower.extendPrime p prime).terminalWindow := by
  exact tower.terminalLayer.extendPrime_new_window p prime

theorem terminal_window_member_prime (tower : FinitePhaseEnergyTower)
    {p : Nat} :
    PrimeWindow.mem p tower.terminalWindow -> IsPrime p := by
  intro member
  exact tower.terminalLayer.window_member_prime member

theorem terminal_parity_readout (tower : FinitePhaseEnergyTower) :
    tower.terminalParity = natParity tower.terminalEnergy := by
  rfl

def fromFinitePrimeTower (T : FinitePrimeTower) :
    FinitePhaseEnergyTower :=
  singleton {
    window := T.completedWindow
    energy := T.layerCount
    bound := T.layerCount
    energy_bounded := Nat.le_refl T.layerCount
  }

theorem fromFinitePrimeTower_terminal_window_elems (T : FinitePrimeTower) :
    (fromFinitePrimeTower T).terminalWindow.elems =
      T.completedWindow.elems := by
  rfl

theorem fromFinitePrimeTower_terminal_energy (T : FinitePrimeTower) :
    (fromFinitePrimeTower T).terminalEnergy = T.layerCount := by
  rfl

theorem fromFinitePrimeTower_terminal_energy_bounded (T : FinitePrimeTower) :
    (fromFinitePrimeTower T).terminalEnergy ≤
      (fromFinitePrimeTower T).terminalBound := by
  exact terminal_energy_bounded (fromFinitePrimeTower T)

theorem fromFinitePrimeTower_terminal_parity (T : FinitePrimeTower) :
    (fromFinitePrimeTower T).terminalParity = natParity T.layerCount := by
  rfl

theorem fromFinitePrimeTower_base_window_included
    (T : FinitePrimeTower) :
    WindowIncluded T.base (fromFinitePrimeTower T).terminalWindow := by
  intro p member
  exact T.base_mem_completed member

theorem fromFinitePrimeTower_addition_window_member
    (T : FinitePrimeTower) {p : Nat} :
    p ∈ T.additions ->
      PrimeWindow.mem p (fromFinitePrimeTower T).terminalWindow := by
  intro member
  exact T.addition_mem_completed member

structure FinitePrimeTowerPhaseReadoutFor (T : FinitePrimeTower) where
  tower : FinitePhaseEnergyTower
  completed_window : tower.terminalWindow.elems = T.completedWindow.elems
  completed_energy : tower.terminalEnergy = T.layerCount
  completed_bound : tower.terminalBound = T.layerCount
  base_included : WindowIncluded T.base tower.terminalWindow

def finitePrimeTowerPhaseReadout (T : FinitePrimeTower) :
    FinitePrimeTowerPhaseReadoutFor T where
  tower := fromFinitePrimeTower T
  completed_window := rfl
  completed_energy := rfl
  completed_bound := rfl
  base_included := fromFinitePrimeTower_base_window_included T

theorem finitePrimeTowerPhaseReadout_energy_bounded
    (T : FinitePrimeTower) :
    (finitePrimeTowerPhaseReadout T).tower.terminalEnergy ≤
      (finitePrimeTowerPhaseReadout T).tower.terminalBound := by
  exact terminal_energy_bounded (finitePrimeTowerPhaseReadout T).tower

end FinitePhaseEnergyTower

/--
向无限方向的相容延拓只给每个 fuel 的有限层和相邻相容见证。
本结构不包含无限素窗口、极限值或 apophatic socket。
-/
structure PhaseEnergyCompatibleExtension where
  layer : Nat -> FinitePhaseEnergyLayer
  step : (n : Nat) -> PhaseEnergyExtensionStep (layer n) (layer (Nat.succ n))

namespace PhaseEnergyCompatibleExtension

theorem layer_energy_monotone (extension : PhaseEnergyCompatibleExtension)
    (n : Nat) :
    (extension.layer n).energy ≤
      (extension.layer (Nat.succ n)).energy :=
  (extension.step n).energy_monotone

theorem layer_energy_bounded (extension : PhaseEnergyCompatibleExtension)
    (n : Nat) :
    (extension.layer n).energy ≤ (extension.layer n).bound :=
  (extension.layer n).energy_le_bound

theorem layer_window_included (extension : PhaseEnergyCompatibleExtension)
    (n p : Nat) :
    PrimeWindow.mem p (extension.layer n).window ->
      PrimeWindow.mem p (extension.layer (Nat.succ n)).window := by
  intro member
  exact (extension.step n).window_included p member

theorem layer_window_member_prime (extension : PhaseEnergyCompatibleExtension)
    (n p : Nat) :
    PrimeWindow.mem p (extension.layer n).window -> IsPrime p := by
  intro member
  exact (extension.layer n).window_member_prime member

theorem layer_parity_readout (extension : PhaseEnergyCompatibleExtension)
    (n : Nat) :
    (extension.layer n).parity = natParity (extension.layer n).energy := by
  rfl

end PhaseEnergyCompatibleExtension

end BEDC.Derived.RHRoute.FiniteToInfinitePhaseEnergyTower
