import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceBoundaryUp : Type where
  | packet :
      (registry exportDecision refused formalTarget socket transport continuation provenance
        name : BHist) →
      MachineInterfaceBoundaryUp
  deriving DecidableEq

def machineInterfaceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineInterfaceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineInterfaceBoundaryEncodeBHist h

def machineInterfaceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineInterfaceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineInterfaceBoundaryDecodeBHist tail)

private theorem machineInterfaceBoundary_decode_encode_bhist :
    ∀ h : BHist, machineInterfaceBoundaryDecodeBHist
      (machineInterfaceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem machineInterfaceBoundary_mk_congr
    {registry registry' exportDecision exportDecision' refused refused'
      formalTarget formalTarget' socket socket' transport transport'
      continuation continuation' provenance provenance' name name' : BHist}
    (hRegistry : registry' = registry)
    (hExportDecision : exportDecision' = exportDecision)
    (hRefused : refused' = refused)
    (hFormalTarget : formalTarget' = formalTarget)
    (hSocket : socket' = socket)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    MachineInterfaceBoundaryUp.packet registry' exportDecision' refused' formalTarget' socket'
        transport' continuation' provenance' name' =
      MachineInterfaceBoundaryUp.packet registry exportDecision refused formalTarget socket
        transport continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRegistry
  cases hExportDecision
  cases hRefused
  cases hFormalTarget
  cases hSocket
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def machineInterfaceBoundaryFields : MachineInterfaceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceBoundaryUp.packet registry exportDecision refused formalTarget socket
      transport continuation provenance name =>
      [registry, exportDecision, refused, formalTarget, socket, transport, continuation,
        provenance, name]

def machineInterfaceBoundaryToEventFlow : MachineInterfaceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MachineInterfaceBoundaryUp.packet registry exportDecision refused formalTarget socket
      transport continuation provenance name =>
      [machineInterfaceBoundaryEncodeBHist registry,
        machineInterfaceBoundaryEncodeBHist exportDecision,
        machineInterfaceBoundaryEncodeBHist refused,
        machineInterfaceBoundaryEncodeBHist formalTarget,
        machineInterfaceBoundaryEncodeBHist socket,
        machineInterfaceBoundaryEncodeBHist transport,
        machineInterfaceBoundaryEncodeBHist continuation,
        machineInterfaceBoundaryEncodeBHist provenance,
        machineInterfaceBoundaryEncodeBHist name]

private def machineInterfaceBoundaryNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => machineInterfaceBoundaryNthRawEvent tail n

def machineInterfaceBoundaryFromEventFlow (ef : EventFlow) :
    Option MachineInterfaceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MachineInterfaceBoundaryUp.packet
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 0))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 1))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 2))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 3))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 4))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 5))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 6))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 7))
      (machineInterfaceBoundaryDecodeBHist (machineInterfaceBoundaryNthRawEvent ef 8)))

private theorem machineInterfaceBoundary_round_trip :
    ∀ x : MachineInterfaceBoundaryUp,
      machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet registry exportDecision refused formalTarget socket transport continuation provenance
      name =>
      exact
        congrArg some
          (machineInterfaceBoundary_mk_congr
            (machineInterfaceBoundary_decode_encode_bhist registry)
            (machineInterfaceBoundary_decode_encode_bhist exportDecision)
            (machineInterfaceBoundary_decode_encode_bhist refused)
            (machineInterfaceBoundary_decode_encode_bhist formalTarget)
            (machineInterfaceBoundary_decode_encode_bhist socket)
            (machineInterfaceBoundary_decode_encode_bhist transport)
            (machineInterfaceBoundary_decode_encode_bhist continuation)
            (machineInterfaceBoundary_decode_encode_bhist provenance)
            (machineInterfaceBoundary_decode_encode_bhist name))

private theorem machineInterfaceBoundaryToEventFlow_injective
    {x y : MachineInterfaceBoundaryUp} :
    machineInterfaceBoundaryToEventFlow x = machineInterfaceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow x) =
        machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow y) :=
    congrArg machineInterfaceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (machineInterfaceBoundary_round_trip x).symm
      (Eq.trans hread (machineInterfaceBoundary_round_trip y)))

private theorem machineInterfaceBoundary_field_faithful :
    ∀ x y : MachineInterfaceBoundaryUp,
      machineInterfaceBoundaryFields x = machineInterfaceBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet registry exportDecision refused formalTarget socket transport continuation provenance
      name =>
      cases y with
      | packet registry' exportDecision' refused' formalTarget' socket' transport'
          continuation' provenance' name' =>
          cases hfields
          rfl

instance machineInterfaceBoundaryBHistCarrier : BHistCarrier MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineInterfaceBoundaryToEventFlow
  fromEventFlow := machineInterfaceBoundaryFromEventFlow

instance machineInterfaceBoundaryChapterTasteGate :
    ChapterTasteGate MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change machineInterfaceBoundaryFromEventFlow (machineInterfaceBoundaryToEventFlow x) =
      some x
    exact machineInterfaceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceBoundaryToEventFlow_injective heq)

instance machineInterfaceBoundaryFieldFaithful :
    FieldFaithful MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := machineInterfaceBoundaryFields
  field_faithful := machineInterfaceBoundary_field_faithful

instance machineInterfaceBoundaryNontrivial : Nontrivial MachineInterfaceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineInterfaceBoundaryUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineInterfaceBoundaryUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MachineInterfaceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  machineInterfaceBoundaryChapterTasteGate

end BEDC.Derived.MachineInterfaceBoundaryUp
