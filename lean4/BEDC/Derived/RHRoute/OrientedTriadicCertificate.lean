import BEDC.Derived.RHRoute.ParityClosureTowerCertificate
import BEDC.Derived.RHRoute.TriadicClosureTower

namespace BEDC.Derived.RHRoute.OrientedTriadicCertificate

open BEDC.Derived.OnticCollapseModes
open BEDC.Derived.UnifiedRelationAtlasUp
open BEDC.Derived.RHRoute.EndpointBisectionCertificate
open BEDC.Derived.RHRoute.RecursiveParityTower
open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.TriadicClosureTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

/-!
本模块登记定向三元证书系统的有限 kernel-side 形状。

它只证明由构造给出的方向、trace、fuel、parity 与 endpoint 行一致。
无限闭包、RH 路线完备性、以及 vision 层的系统元定理留在
`BEDC.Boundary.OrientedTriadicCertificate` 中作为外部待供给行。
-/

inductive OrientedTriadicEdge where
  | distinctionToTime
  | timeToSymmetry
  | distinctionToSymmetry

def OrientedTriadicEdge.source
    (axes : OnticAxisTriple) : OrientedTriadicEdge -> OnticAxis
  | OrientedTriadicEdge.distinctionToTime => axes.distinctionAxis
  | OrientedTriadicEdge.timeToSymmetry => axes.timeAxis
  | OrientedTriadicEdge.distinctionToSymmetry => axes.distinctionAxis

def OrientedTriadicEdge.target
    (axes : OnticAxisTriple) : OrientedTriadicEdge -> OnticAxis
  | OrientedTriadicEdge.distinctionToTime => axes.timeAxis
  | OrientedTriadicEdge.timeToSymmetry => axes.symmetryAxis
  | OrientedTriadicEdge.distinctionToSymmetry => axes.symmetryAxis

def OrientedTriadicEdge.sourceSlot : OrientedTriadicEdge -> TriadicAxisSlot
  | OrientedTriadicEdge.distinctionToTime => TriadicAxisSlot.distinction
  | OrientedTriadicEdge.timeToSymmetry => TriadicAxisSlot.time
  | OrientedTriadicEdge.distinctionToSymmetry => TriadicAxisSlot.distinction

def OrientedTriadicEdge.targetSlot : OrientedTriadicEdge -> TriadicAxisSlot
  | OrientedTriadicEdge.distinctionToTime => TriadicAxisSlot.time
  | OrientedTriadicEdge.timeToSymmetry => TriadicAxisSlot.symmetry
  | OrientedTriadicEdge.distinctionToSymmetry => TriadicAxisSlot.symmetry

def orientedTriadicEdgeProgram : List OrientedTriadicEdge :=
  [ OrientedTriadicEdge.distinctionToTime,
    OrientedTriadicEdge.timeToSymmetry,
    OrientedTriadicEdge.distinctionToSymmetry ]

def orientedTriadicSourceSlots : List TriadicAxisSlot :=
  orientedTriadicEdgeProgram.map OrientedTriadicEdge.sourceSlot

def orientedTriadicTargetSlots : List TriadicAxisSlot :=
  orientedTriadicEdgeProgram.map OrientedTriadicEdge.targetSlot

theorem orientedTriadicSourceSlots_readback :
    orientedTriadicSourceSlots =
      [TriadicAxisSlot.distinction,
        TriadicAxisSlot.time,
        TriadicAxisSlot.distinction] := by
  rfl

theorem orientedTriadicTargetSlots_readback :
    orientedTriadicTargetSlots =
      [TriadicAxisSlot.time,
        TriadicAxisSlot.symmetry,
        TriadicAxisSlot.symmetry] := by
  rfl

theorem orientedTriadicEdgeProgram_length :
    orientedTriadicEdgeProgram.length = 3 := by
  rfl

theorem orientedTriadicSourceSlots_length :
    orientedTriadicSourceSlots.length = 3 := by
  rfl

theorem orientedTriadicTargetSlots_length :
    orientedTriadicTargetSlots.length = 3 := by
  rfl

structure OrientedTriadicAxisCertificate
    (axes : OnticAxisTriple) where
  axes_marked : axes.Marked
  edge_program : List OrientedTriadicEdge
  edge_program_readback : edge_program = orientedTriadicEdgeProgram
  source_slots_readback :
    edge_program.map OrientedTriadicEdge.sourceSlot =
      [TriadicAxisSlot.distinction,
        TriadicAxisSlot.time,
        TriadicAxisSlot.distinction]
  target_slots_readback :
    edge_program.map OrientedTriadicEdge.targetSlot =
      [TriadicAxisSlot.time,
        TriadicAxisSlot.symmetry,
        TriadicAxisSlot.symmetry]

namespace OrientedTriadicAxisCertificate

def sourceAxes (cert : OrientedTriadicAxisCertificate axes) :
    List OnticAxis :=
  cert.edge_program.map (fun edge => edge.source axes)

def targetAxes (cert : OrientedTriadicAxisCertificate axes) :
    List OnticAxis :=
  cert.edge_program.map (fun edge => edge.target axes)

def Invariant (cert : OrientedTriadicAxisCertificate axes) : Prop :=
  axes.Marked ∧
    cert.edge_program = orientedTriadicEdgeProgram ∧
      cert.source_slots_readback =
        Eq.trans (congrArg (List.map OrientedTriadicEdge.sourceSlot)
          cert.edge_program_readback) orientedTriadicSourceSlots_readback ∧
        cert.target_slots_readback =
          Eq.trans (congrArg (List.map OrientedTriadicEdge.targetSlot)
            cert.edge_program_readback) orientedTriadicTargetSlots_readback

theorem invariant
    (cert : OrientedTriadicAxisCertificate axes) :
    cert.Invariant := by
  exact ⟨cert.axes_marked, cert.edge_program_readback, rfl, rfl⟩

end OrientedTriadicAxisCertificate

def canonicalOrientedTriadicAxisCertificate :
    OrientedTriadicAxisCertificate canonicalOnticAxisTriple where
  axes_marked := canonicalOnticAxisTriple_marked
  edge_program := orientedTriadicEdgeProgram
  edge_program_readback := rfl
  source_slots_readback := orientedTriadicSourceSlots_readback
  target_slots_readback := orientedTriadicTargetSlots_readback

theorem canonicalOrientedTriadicAxisCertificate_invariant :
    canonicalOrientedTriadicAxisCertificate.Invariant := by
  exact OrientedTriadicAxisCertificate.invariant
    canonicalOrientedTriadicAxisCertificate

structure OrientedTriadicStepCertificate
    (step : TriadicClosureStep) where
  axis_certificate : OrientedTriadicAxisCertificate canonicalOnticAxisTriple
  closed_over_triad : step.closedOverTriad
  event_stack_length : step.eventStack.length = 3
  program_events_length : step.programEvents.length = 3

namespace OrientedTriadicStepCertificate

def canonical (step : TriadicClosureStep) :
    OrientedTriadicStepCertificate step where
  axis_certificate := canonicalOrientedTriadicAxisCertificate
  closed_over_triad := TriadicClosureStep.closed_over_triad step
  event_stack_length := TriadicClosureStep.eventStack_length step
  program_events_length := TriadicClosureStep.programEvents_length step

def Invariant {step : TriadicClosureStep}
    (cert : OrientedTriadicStepCertificate step) : Prop :=
  cert.axis_certificate.Invariant ∧
    step.closedOverTriad ∧
      step.eventStack.length = 3 ∧
        step.programEvents.length = 3

theorem invariant {step : TriadicClosureStep}
    (cert : OrientedTriadicStepCertificate step) :
    cert.Invariant := by
  exact ⟨OrientedTriadicAxisCertificate.invariant cert.axis_certificate,
    cert.closed_over_triad, cert.event_stack_length,
    cert.program_events_length⟩

end OrientedTriadicStepCertificate

inductive OrientedTriadicStepCertificates :
    List TriadicClosureStep -> Type where
  | nil : OrientedTriadicStepCertificates []
  | cons {steps : List TriadicClosureStep}
      (step : TriadicClosureStep)
      (row : OrientedTriadicStepCertificate step)
      (rest : OrientedTriadicStepCertificates steps) :
      OrientedTriadicStepCertificates (step :: steps)

namespace OrientedTriadicStepCertificates

def canonical :
    (steps : List TriadicClosureStep) ->
      OrientedTriadicStepCertificates steps
  | [] => OrientedTriadicStepCertificates.nil
  | step :: steps =>
      OrientedTriadicStepCertificates.cons step
        (OrientedTriadicStepCertificate.canonical step)
        (canonical steps)

def rowCount :
    {steps : List TriadicClosureStep} ->
      OrientedTriadicStepCertificates steps -> Nat
  | [], OrientedTriadicStepCertificates.nil => 0
  | _ :: _, OrientedTriadicStepCertificates.cons _ _ rest =>
      Nat.succ (rowCount rest)

def Invariant :
    {steps : List TriadicClosureStep} ->
      OrientedTriadicStepCertificates steps -> Prop
  | [], OrientedTriadicStepCertificates.nil =>
      rowCount OrientedTriadicStepCertificates.nil = 0
  | _step :: _steps, OrientedTriadicStepCertificates.cons _ row rest =>
      row.Invariant ∧ Invariant rest

theorem invariant :
    {steps : List TriadicClosureStep} ->
      (certs : OrientedTriadicStepCertificates steps) ->
        certs.Invariant
  | [], OrientedTriadicStepCertificates.nil =>
      rfl
  | _step :: _steps, OrientedTriadicStepCertificates.cons _ row rest =>
      ⟨OrientedTriadicStepCertificate.invariant row, invariant rest⟩

theorem rowCount_length :
    {steps : List TriadicClosureStep} ->
      (certs : OrientedTriadicStepCertificates steps) ->
        certs.rowCount = steps.length
  | [], OrientedTriadicStepCertificates.nil =>
      rfl
  | _step :: _steps, OrientedTriadicStepCertificates.cons _ _ rest =>
      congrArg Nat.succ (rowCount_length rest)

end OrientedTriadicStepCertificates

inductive OrientedTriadicSystemScope where
  | finiteProgramSpecification

structure OrientedTriadicCertificateSystem
    (signature : RHFreeZeroSignature) where
  program : TriadicClosureProgram signature
  scope : OrientedTriadicSystemScope
  scope_spec : scope = OrientedTriadicSystemScope.finiteProgramSpecification
  program_scope :
    program.scope = TriadicClosureClaimScope.finiteProgramSpecification
  endpoint_choose : Nat -> EndpointBisectionCertificate.EndpointBranch
  axis_certificate : OrientedTriadicAxisCertificate program.axes
  step_certificates : OrientedTriadicStepCertificates program.steps
  parity_certificate :
    BEDC.Derived.RHRoute.ParityClosureTowerCertificate.ParityClosureTowerCertificate
      program.tower

namespace OrientedTriadicCertificateSystem

def canonical {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (steps : List TriadicClosureStep)
    (endpoint_choose : Nat ->
      EndpointBisectionCertificate.EndpointBranch) :
    OrientedTriadicCertificateSystem signature where
  program := TriadicClosureProgram.canonical seedLayer steps
  scope := OrientedTriadicSystemScope.finiteProgramSpecification
  scope_spec := rfl
  program_scope := rfl
  endpoint_choose := endpoint_choose
  axis_certificate := canonicalOrientedTriadicAxisCertificate
  step_certificates := OrientedTriadicStepCertificates.canonical steps
  parity_certificate :=
    BEDC.Derived.RHRoute.ParityClosureTowerCertificate.ParityClosureTowerCertificate.buildCanonical
      endpoint_choose
      (TriadicClosureProgram.tower
        (TriadicClosureProgram.canonical seedLayer steps))

def terminalTower {signature : RHFreeZeroSignature}
    (system : OrientedTriadicCertificateSystem signature) :
    RecursiveParityTower signature
      (RecursiveParityTower.natParity system.program.trace.length) :=
  system.program.tower

def terminalTrace {signature : RHFreeZeroSignature}
    (system : OrientedTriadicCertificateSystem signature) :
    List TraceEvent :=
  RecursiveParityTower.recursiveEvents system.terminalTower

def terminalEndpoint {signature : RHFreeZeroSignature}
    (system : OrientedTriadicCertificateSystem signature) :
    EndpointBisectionCertificate.EndpointDyadicInterval :=
  BEDC.Derived.RHRoute.ParityClosureTowerCertificate.ParityClosureTowerCertificate.endpoint
    system.parity_certificate

end OrientedTriadicCertificateSystem

structure OrientedTriadicSystemInvariant
    {signature : RHFreeZeroSignature}
    (system : OrientedTriadicCertificateSystem signature) : Prop where
  scope_is_finite_program :
    system.scope = OrientedTriadicSystemScope.finiteProgramSpecification
  program_is_finite_spec :
    system.program.scope = TriadicClosureClaimScope.finiteProgramSpecification
  axis_certificate_sound :
    system.axis_certificate.Invariant
  step_certificates_sound :
    system.step_certificates.Invariant
  step_rows_cover_program :
    system.step_certificates.rowCount = system.program.steps.length
  program_closure :
    system.program.ClosureInvariant
  finite_tower :
    BEDC.Derived.RHRoute.ParityClosureTowerCertificate.ParityClosureTowerInvariant
      system.program.tower system.parity_certificate
  terminal_trace_matches_program :
    system.terminalTrace = system.program.trace
  terminal_endpoint_contract :
    EndpointDyadicDiameterContract
      system.terminalEndpoint
      (RecursiveParityTower.depth system.program.tower)

theorem orientedTriadicSystemInvariant
    {signature : RHFreeZeroSignature}
    (system : OrientedTriadicCertificateSystem signature) :
    OrientedTriadicSystemInvariant system := by
  constructor
  · exact system.scope_spec
  · exact system.program_scope
  · exact OrientedTriadicAxisCertificate.invariant
      system.axis_certificate
  · exact OrientedTriadicStepCertificates.invariant
      system.step_certificates
  · exact OrientedTriadicStepCertificates.rowCount_length
      system.step_certificates
  · exact TriadicClosureProgram.closure_invariant
      system.program system.program_scope
  · exact
      BEDC.Derived.RHRoute.ParityClosureTowerCertificate.finiteParityClosureTowerInvariant
        system.parity_certificate
  · change
      RecursiveParityTower.recursiveEvents
        (RecursiveParityTower.buildFromTrace
          system.program.seedLayer system.program.trace) =
        system.program.trace
    exact RecursiveParityTower.buildFromTrace_events
      system.program.seedLayer system.program.trace
  · exact
      BEDC.Derived.RHRoute.ParityClosureTowerCertificate.ParityClosureTowerCertificate.terminal_endpoint_contract
        system.parity_certificate

theorem canonicalOrientedTriadicSystemInvariant
    {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (steps : List TriadicClosureStep)
    (endpoint_choose : Nat ->
      EndpointBisectionCertificate.EndpointBranch) :
    OrientedTriadicSystemInvariant
      (OrientedTriadicCertificateSystem.canonical
        seedLayer steps endpoint_choose) := by
  exact orientedTriadicSystemInvariant
    (OrientedTriadicCertificateSystem.canonical
      seedLayer steps endpoint_choose)

def buildCanonicalOrientedTriadicSystem
    {signature : RHFreeZeroSignature}
    (seedLayer : SpectralZeroLayer signature)
    (steps : List TriadicClosureStep)
    (endpoint_choose : Nat ->
      EndpointBisectionCertificate.EndpointBranch) :
    Subtype
      (fun system : OrientedTriadicCertificateSystem signature =>
        OrientedTriadicSystemInvariant system) :=
  Subtype.mk
    (OrientedTriadicCertificateSystem.canonical
      seedLayer steps endpoint_choose)
    (canonicalOrientedTriadicSystemInvariant
      seedLayer steps endpoint_choose)

end BEDC.Derived.RHRoute.OrientedTriadicCertificate
