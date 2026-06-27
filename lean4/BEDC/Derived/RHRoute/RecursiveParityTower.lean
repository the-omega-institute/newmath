import BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy

namespace BEDC.Derived.RHRoute.RecursiveParityTower

open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

-- 上游模块名含 spectral；这里仅登记有限递归塔与层宇称。
inductive TowerParity where
  | even
  | odd

def flip : TowerParity -> TowerParity
  | TowerParity.even => TowerParity.odd
  | TowerParity.odd => TowerParity.even

theorem flip_involutive (p : TowerParity) :
    flip (flip p) = p := by
  cases p <;> rfl

def natParity : Nat -> TowerParity
  | 0 => TowerParity.even
  | Nat.succ n => flip (natParity n)

theorem natParity_succ (n : Nat) :
    natParity (Nat.succ n) = flip (natParity n) := by
  rfl

theorem natParity_two_step (n : Nat) :
    natParity (Nat.succ (Nat.succ n)) = natParity n := by
  change flip (flip (natParity n)) = natParity n
  exact flip_involutive (natParity n)

inductive RecursiveParityTower
    (signature : RHFreeZeroSignature) : TowerParity -> Type where
  | seed :
      SpectralZeroLayer signature ->
        RecursiveParityTower signature TowerParity.even
  | step {p : TowerParity} :
      TraceEvent ->
        RecursiveParityTower signature p ->
          RecursiveParityTower signature (flip p)

namespace RecursiveParityTower

def depth {signature : RHFreeZeroSignature} {p : TowerParity} :
    RecursiveParityTower signature p -> Nat
  | seed _ => 0
  | step _ prior => Nat.succ (depth prior)

def root {signature : RHFreeZeroSignature} {p : TowerParity} :
    RecursiveParityTower signature p -> SpectralZeroLayer signature
  | seed z => z
  | step _ prior => root prior

def top {signature : RHFreeZeroSignature} {p : TowerParity} :
    RecursiveParityTower signature p -> SpectralZeroLayer signature
  | seed z => z
  | step event prior =>
      SpectralZeroLayer.recursiveTowerReadback event (top prior)

def recursiveEvents {signature : RHFreeZeroSignature} {p : TowerParity} :
    RecursiveParityTower signature p -> List TraceEvent
  | seed _ => []
  | step event prior => event :: recursiveEvents prior

def fullTrace {signature : RHFreeZeroSignature} {p : TowerParity} :
    RecursiveParityTower signature p -> List TraceEvent
  | seed z => layerTrace z
  | step event prior => event :: fullTrace prior

def forget {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p) : GeneratedZero signature :=
  forgetToGeneratedZero (top tower)

def LayerParityInvariant {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p) : Prop :=
  p = natParity (depth tower)

theorem depth_parity {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p) :
    LayerParityInvariant tower := by
  induction tower with
  | seed _ =>
      rfl
  | step _ prior ih =>
      change flip _ = flip (natParity (depth prior))
      exact congrArg flip ih

theorem step_depth {signature : RHFreeZeroSignature} {p : TowerParity}
    (event : TraceEvent) (tower : RecursiveParityTower signature p) :
    depth (step event tower) = Nat.succ (depth tower) := by
  rfl

theorem step_root {signature : RHFreeZeroSignature} {p : TowerParity}
    (event : TraceEvent) (tower : RecursiveParityTower signature p) :
    root (step event tower) = root tower := by
  rfl

theorem step_top {signature : RHFreeZeroSignature} {p : TowerParity}
    (event : TraceEvent) (tower : RecursiveParityTower signature p) :
    top (step event tower) =
      SpectralZeroLayer.recursiveTowerReadback event (top tower) := by
  rfl

theorem step_forget {signature : RHFreeZeroSignature} {p : TowerParity}
    (event : TraceEvent) (tower : RecursiveParityTower signature p) :
    forget (step event tower) =
      GeneratedZero.recursiveTowerReadback event (forget tower) := by
  rfl

theorem step_top_depth {signature : RHFreeZeroSignature} {p : TowerParity}
    (event : TraceEvent) (tower : RecursiveParityTower signature p) :
    layerDepth (top (step event tower)) =
      Nat.succ (layerDepth (top tower)) := by
  rfl

theorem step_fullTrace {signature : RHFreeZeroSignature} {p : TowerParity}
    (event : TraceEvent) (tower : RecursiveParityTower signature p) :
    fullTrace (step event tower) = event :: fullTrace tower := by
  rfl

theorem fullTrace_sound {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p) :
    layerTrace (top tower) = fullTrace tower := by
  induction tower with
  | seed _ =>
      rfl
  | step event prior ih =>
      change event :: layerTrace (top prior) = event :: fullTrace prior
      exact congrArg (fun trace => event :: trace) ih

theorem top_atDepth {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p) :
    AtDepth (layerDepth (top tower)) (top tower) := by
  rfl

def buildWithFuel {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature) :
    (fuel : Nat) -> (eventAt : Nat -> TraceEvent) ->
      RecursiveParityTower signature (natParity fuel)
  | 0, _eventAt => seed seedLayer
  | Nat.succ fuel, eventAt =>
      step (eventAt fuel) (buildWithFuel seedLayer fuel eventAt)

theorem buildWithFuel_depth {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (fuel : Nat) (eventAt : Nat -> TraceEvent) :
    depth (buildWithFuel seedLayer fuel eventAt) = fuel := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      change Nat.succ (depth (buildWithFuel seedLayer fuel eventAt)) =
        Nat.succ fuel
      exact congrArg Nat.succ ih

theorem buildWithFuel_parity {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (fuel : Nat) (eventAt : Nat -> TraceEvent) :
    LayerParityInvariant (buildWithFuel seedLayer fuel eventAt) := by
  exact depth_parity (buildWithFuel seedLayer fuel eventAt)

def buildFromTrace {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature) :
    (events : List TraceEvent) ->
      RecursiveParityTower signature (natParity events.length)
  | [] => seed seedLayer
  | event :: events => step event (buildFromTrace seedLayer events)

theorem buildFromTrace_depth {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (events : List TraceEvent) :
    depth (buildFromTrace seedLayer events) = events.length := by
  induction events with
  | nil =>
      rfl
  | cons event events ih =>
      change Nat.succ (depth (buildFromTrace seedLayer events)) =
        Nat.succ events.length
      exact congrArg Nat.succ ih

theorem buildFromTrace_events {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (events : List TraceEvent) :
    recursiveEvents (buildFromTrace seedLayer events) = events := by
  induction events with
  | nil =>
      rfl
  | cons event events ih =>
      change event :: recursiveEvents (buildFromTrace seedLayer events) =
        event :: events
      exact congrArg (fun trace => event :: trace) ih

theorem buildFromTrace_parity {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (events : List TraceEvent) :
    LayerParityInvariant (buildFromTrace seedLayer events) := by
  exact depth_parity (buildFromTrace seedLayer events)

end RecursiveParityTower

end BEDC.Derived.RHRoute.RecursiveParityTower
