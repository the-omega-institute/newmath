import BEDC.Derived.RHRoute.RecursiveParityTower
import BEDC.Derived.UnifiedRelationAtlasUp

namespace BEDC.Derived.RHRoute.TriadicClosureTower

open BEDC.Derived.OnticCollapseModes
open BEDC.Derived.UnifiedRelationAtlasUp
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.RecursiveParityTower

/-!
本模块只给出有限三元闭包塔的 kernel-side 规格化程序。
它记录 distinction/time/symmetry 三轴如何附着到已有递归 parity tower,
并证明由构造带来的 trace、depth、parity 不变量。这里不证明 RH,
也不证明 vision 层的元理论完备性。
-/

inductive TriadicAxisSlot where
  | distinction
  | time
  | symmetry
  deriving DecidableEq

def TriadicAxisSlot.toOnticAxis : TriadicAxisSlot -> OnticAxis
  | TriadicAxisSlot.distinction => OnticAxis.distinction
  | TriadicAxisSlot.time => OnticAxis.time
  | TriadicAxisSlot.symmetry => OnticAxis.symmetry

def triadicAxisProgramOrder : List TriadicAxisSlot :=
  [TriadicAxisSlot.distinction, TriadicAxisSlot.time, TriadicAxisSlot.symmetry]

def triadicOnticAxisProgramOrder : List OnticAxis :=
  triadicAxisProgramOrder.map TriadicAxisSlot.toOnticAxis

def TriadicAxisSlot.code : TriadicAxisSlot -> Nat
  | TriadicAxisSlot.distinction => 0
  | TriadicAxisSlot.time => 1
  | TriadicAxisSlot.symmetry => 2

def countTriadicAxisCode (needle : Nat) : List TriadicAxisSlot -> Nat
  | [] => 0
  | axis :: rest =>
      match Nat.beq needle axis.code with
      | true => Nat.succ (countTriadicAxisCode needle rest)
      | false => countTriadicAxisCode needle rest

def countTriadicAxis (needle : TriadicAxisSlot)
    (axes : List TriadicAxisSlot) : Nat :=
  countTriadicAxisCode needle.code axes

def AxisInTriple (axes : OnticAxisTriple) (axis : OnticAxis) : Prop :=
  axis = axes.distinctionAxis ∨
    axis = axes.timeAxis ∨
      axis = axes.symmetryAxis

theorem triadicAxisProgramOrder_counts :
    countTriadicAxis TriadicAxisSlot.distinction triadicAxisProgramOrder = 1 ∧
      countTriadicAxis TriadicAxisSlot.time triadicAxisProgramOrder = 1 ∧
        countTriadicAxis TriadicAxisSlot.symmetry triadicAxisProgramOrder = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem triadicAxisProgramOrder_nodup :
    triadicAxisProgramOrder.Nodup := by
  decide

theorem triadicOnticAxisProgramOrder_readback :
    triadicOnticAxisProgramOrder =
      [OnticAxis.distinction, OnticAxis.time, OnticAxis.symmetry] := by
  rfl

theorem slot_axis_in_marked_triple
    (axes : OnticAxisTriple) (marked : axes.Marked)
    (slot : TriadicAxisSlot) :
    AxisInTriple axes slot.toOnticAxis := by
  cases slot with
  | distinction =>
      exact Or.inl marked.left.symm
  | time =>
      exact Or.inr (Or.inl marked.right.left.symm)
  | symmetry =>
      exact Or.inr (Or.inr marked.right.right.symm)

abbrev ParityTower (signature : RHFreeZeroSignature)
    (parity : TowerParity) : Type :=
  RecursiveParityTower signature parity

structure TriadicClosureLayer (signature : RHFreeZeroSignature) where
  parity : TowerParity
  tower : ParityTower signature parity
  activeSlot : TriadicAxisSlot
  axes : OnticAxisTriple
  axes_marked : axes.Marked

namespace TriadicClosureLayer

def depth {signature : RHFreeZeroSignature}
    (layer : TriadicClosureLayer signature) : Nat :=
  RecursiveParityTower.depth layer.tower

def top {signature : RHFreeZeroSignature}
    (layer : TriadicClosureLayer signature) :
    SpectralZeroLayer signature :=
  RecursiveParityTower.top layer.tower

def recursiveEvents {signature : RHFreeZeroSignature}
    (layer : TriadicClosureLayer signature) : List TraceEvent :=
  RecursiveParityTower.recursiveEvents layer.tower

def ClosureInvariant {signature : RHFreeZeroSignature}
    (layer : TriadicClosureLayer signature) : Prop :=
  AxisInTriple layer.axes layer.activeSlot.toOnticAxis ∧
    RecursiveParityTower.LayerParityInvariant layer.tower

theorem closure_invariant {signature : RHFreeZeroSignature}
    (layer : TriadicClosureLayer signature) :
    layer.ClosureInvariant := by
  exact ⟨slot_axis_in_marked_triple layer.axes layer.axes_marked layer.activeSlot,
    RecursiveParityTower.depth_parity layer.tower⟩

end TriadicClosureLayer

structure TriadicClosureStep where
  distinctionEvent : TraceEvent
  timeEvent : TraceEvent
  symmetryEvent : TraceEvent

namespace TriadicClosureStep

def axisOrder (_step : TriadicClosureStep) : List TriadicAxisSlot :=
  triadicAxisProgramOrder

def eventStack (step : TriadicClosureStep) : List TraceEvent :=
  [step.symmetryEvent, step.timeEvent, step.distinctionEvent]

def programEvents (step : TriadicClosureStep) : List TraceEvent :=
  [step.distinctionEvent, step.timeEvent, step.symmetryEvent]

def closedOverTriad (step : TriadicClosureStep) : Prop :=
  step.axisOrder = triadicAxisProgramOrder ∧
    step.axisOrder.Nodup ∧
      countTriadicAxis TriadicAxisSlot.distinction step.axisOrder = 1 ∧
        countTriadicAxis TriadicAxisSlot.time step.axisOrder = 1 ∧
          countTriadicAxis TriadicAxisSlot.symmetry step.axisOrder = 1

theorem closed_over_triad (step : TriadicClosureStep) :
    step.closedOverTriad := by
  exact ⟨rfl, triadicAxisProgramOrder_nodup, triadicAxisProgramOrder_counts⟩

theorem eventStack_length (step : TriadicClosureStep) :
    step.eventStack.length = 3 := by
  rfl

theorem programEvents_length (step : TriadicClosureStep) :
    step.programEvents.length = 3 := by
  rfl

end TriadicClosureStep

def applyTriadicStep {signature : RHFreeZeroSignature} {parity : TowerParity}
    (step : TriadicClosureStep)
    (tower : ParityTower signature parity) :
    ParityTower signature (flip (flip (flip parity))) :=
  RecursiveParityTower.step step.symmetryEvent
    (RecursiveParityTower.step step.timeEvent
      (RecursiveParityTower.step step.distinctionEvent tower))

theorem applyTriadicStep_depth
    {signature : RHFreeZeroSignature} {parity : TowerParity}
    (step : TriadicClosureStep)
    (tower : ParityTower signature parity) :
    RecursiveParityTower.depth (applyTriadicStep step tower) =
      Nat.succ (Nat.succ (Nat.succ (RecursiveParityTower.depth tower))) := by
  rfl

theorem applyTriadicStep_recursiveEvents
    {signature : RHFreeZeroSignature} {parity : TowerParity}
    (step : TriadicClosureStep)
    (tower : ParityTower signature parity) :
    RecursiveParityTower.recursiveEvents (applyTriadicStep step tower) =
      step.eventStack ++ RecursiveParityTower.recursiveEvents tower := by
  rfl

theorem applyTriadicStep_fullTrace
    {signature : RHFreeZeroSignature} {parity : TowerParity}
    (step : TriadicClosureStep)
    (tower : ParityTower signature parity) :
    RecursiveParityTower.fullTrace (applyTriadicStep step tower) =
      step.eventStack ++ RecursiveParityTower.fullTrace tower := by
  rfl

def triadicClosureTrace : List TriadicClosureStep -> List TraceEvent
  | [] => []
  | step :: rest => step.eventStack ++ triadicClosureTrace rest

def triadicClosureFuel : List TriadicClosureStep -> Nat
  | [] => 0
  | _step :: rest => Nat.succ (Nat.succ (Nat.succ (triadicClosureFuel rest)))

theorem triadicClosureTrace_length (steps : List TriadicClosureStep) :
    (triadicClosureTrace steps).length = triadicClosureFuel steps := by
  induction steps with
  | nil =>
      rfl
  | cons step rest ih =>
      change
        Nat.succ (Nat.succ (Nat.succ (triadicClosureTrace rest).length)) =
          Nat.succ (Nat.succ (Nat.succ (triadicClosureFuel rest)))
      exact congrArg Nat.succ (congrArg Nat.succ (congrArg Nat.succ ih))

inductive TriadicClosureClaimScope where
  | finiteProgramSpecification
  | externalMetatheoryBoundary

structure TriadicClosureProgram (signature : RHFreeZeroSignature) where
  seedLayer : SpectralZeroLayer signature
  steps : List TriadicClosureStep
  axes : OnticAxisTriple
  axes_marked : axes.Marked
  scope : TriadicClosureClaimScope

namespace TriadicClosureProgram

def canonical {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (steps : List TriadicClosureStep) :
    TriadicClosureProgram signature where
  seedLayer := seedLayer
  steps := steps
  axes := canonicalOnticAxisTriple
  axes_marked := canonicalOnticAxisTriple_marked
  scope := TriadicClosureClaimScope.finiteProgramSpecification

def trace {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) : List TraceEvent :=
  triadicClosureTrace program.steps

def fuel {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) : Nat :=
  triadicClosureFuel program.steps

def StepClosureInvariant {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) : Prop :=
  ∀ step, step ∈ program.steps -> step.closedOverTriad

def tower {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    ParityTower signature (natParity program.trace.length) :=
  RecursiveParityTower.buildFromTrace program.seedLayer program.trace

def terminalLayer {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    TriadicClosureLayer signature where
  parity := natParity program.trace.length
  tower := program.tower
  activeSlot := TriadicAxisSlot.symmetry
  axes := program.axes
  axes_marked := program.axes_marked

def ClosureInvariant {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) : Prop :=
  program.axes.Marked ∧
    program.scope = TriadicClosureClaimScope.finiteProgramSpecification ∧
      program.StepClosureInvariant ∧
        RecursiveParityTower.depth program.tower = program.fuel ∧
          RecursiveParityTower.LayerParityInvariant program.tower ∧
            (program.terminalLayer).ClosureInvariant

theorem trace_length {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    program.trace.length = program.fuel := by
  exact triadicClosureTrace_length program.steps

theorem step_closure_invariant {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    program.StepClosureInvariant := by
  intro step _membership
  exact TriadicClosureStep.closed_over_triad step

theorem tower_depth {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    RecursiveParityTower.depth program.tower = program.fuel := by
  exact Eq.trans
    (RecursiveParityTower.buildFromTrace_depth program.seedLayer program.trace)
    program.trace_length

theorem tower_parity {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    RecursiveParityTower.LayerParityInvariant program.tower := by
  exact RecursiveParityTower.buildFromTrace_parity program.seedLayer program.trace

theorem terminal_layer_invariant {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature) :
    program.terminalLayer.ClosureInvariant := by
  exact TriadicClosureLayer.closure_invariant program.terminalLayer

theorem closure_invariant {signature : RHFreeZeroSignature}
    (program : TriadicClosureProgram signature)
    (scope_spec :
    program.scope = TriadicClosureClaimScope.finiteProgramSpecification) :
    program.ClosureInvariant := by
  exact ⟨program.axes_marked, scope_spec, program.step_closure_invariant,
    program.tower_depth, program.tower_parity,
    program.terminal_layer_invariant⟩

theorem canonical_closure_invariant {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (steps : List TriadicClosureStep) :
    (canonical seedLayer steps).ClosureInvariant := by
  exact closure_invariant (canonical seedLayer steps) rfl

end TriadicClosureProgram

end BEDC.Derived.RHRoute.TriadicClosureTower
