import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegistryExportConsistencyGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegistryExportConsistencyGateUp : Type where
  | mk :
      (registry blocking status formalTarget audit noSmuggling transport replay provenance
        name : BHist) →
      RegistryExportConsistencyGateUp
  deriving DecidableEq

def registryExportConsistencyGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: registryExportConsistencyGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: registryExportConsistencyGateEncodeBHist h

def registryExportConsistencyGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (registryExportConsistencyGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (registryExportConsistencyGateDecodeBHist tail)

private theorem registryExportConsistencyGate_decode_encode_bhist :
    ∀ h : BHist,
      registryExportConsistencyGateDecodeBHist
        (registryExportConsistencyGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem registryExportConsistencyGate_mk_congr
    {registry registry' blocking blocking' status status' formalTarget formalTarget'
      audit audit' noSmuggling noSmuggling' transport transport' replay replay'
      provenance provenance' name name' : BHist}
    (hRegistry : registry' = registry)
    (hBlocking : blocking' = blocking)
    (hStatus : status' = status)
    (hFormalTarget : formalTarget' = formalTarget)
    (hAudit : audit' = audit)
    (hNoSmuggling : noSmuggling' = noSmuggling)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RegistryExportConsistencyGateUp.mk registry' blocking' status' formalTarget' audit'
        noSmuggling' transport' replay' provenance' name' =
      RegistryExportConsistencyGateUp.mk registry blocking status formalTarget audit
        noSmuggling transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRegistry
  cases hBlocking
  cases hStatus
  cases hFormalTarget
  cases hAudit
  cases hNoSmuggling
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def registryExportConsistencyGateFields :
    RegistryExportConsistencyGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryExportConsistencyGateUp.mk registry blocking status formalTarget audit noSmuggling
      transport replay provenance name =>
      [registry, blocking, status, formalTarget, audit, noSmuggling, transport, replay,
        provenance, name]

def registryExportConsistencyGateToEventFlow :
    RegistryExportConsistencyGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryExportConsistencyGateUp.mk registry blocking status formalTarget audit noSmuggling
      transport replay provenance name =>
      [registryExportConsistencyGateEncodeBHist registry,
        registryExportConsistencyGateEncodeBHist blocking,
        registryExportConsistencyGateEncodeBHist status,
        registryExportConsistencyGateEncodeBHist formalTarget,
        registryExportConsistencyGateEncodeBHist audit,
        registryExportConsistencyGateEncodeBHist noSmuggling,
        registryExportConsistencyGateEncodeBHist transport,
        registryExportConsistencyGateEncodeBHist replay,
        registryExportConsistencyGateEncodeBHist provenance,
        registryExportConsistencyGateEncodeBHist name]

private def registryExportConsistencyGateEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      registryExportConsistencyGateEventAtDefault index rest

def registryExportConsistencyGateFromEventFlow :
    EventFlow → Option RegistryExportConsistencyGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegistryExportConsistencyGateUp.mk
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 0 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 1 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 2 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 3 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 4 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 5 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 6 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 7 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 8 ef))
        (registryExportConsistencyGateDecodeBHist
          (registryExportConsistencyGateEventAtDefault 9 ef)))

private theorem registryExportConsistencyGate_round_trip :
    ∀ x : RegistryExportConsistencyGateUp,
      registryExportConsistencyGateFromEventFlow
        (registryExportConsistencyGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk registry blocking status formalTarget audit noSmuggling transport replay provenance
      name =>
      exact
        congrArg some
          (registryExportConsistencyGate_mk_congr
            (registryExportConsistencyGate_decode_encode_bhist registry)
            (registryExportConsistencyGate_decode_encode_bhist blocking)
            (registryExportConsistencyGate_decode_encode_bhist status)
            (registryExportConsistencyGate_decode_encode_bhist formalTarget)
            (registryExportConsistencyGate_decode_encode_bhist audit)
            (registryExportConsistencyGate_decode_encode_bhist noSmuggling)
            (registryExportConsistencyGate_decode_encode_bhist transport)
            (registryExportConsistencyGate_decode_encode_bhist replay)
            (registryExportConsistencyGate_decode_encode_bhist provenance)
            (registryExportConsistencyGate_decode_encode_bhist name))

private theorem registryExportConsistencyGateToEventFlow_injective
    {x y : RegistryExportConsistencyGateUp} :
    registryExportConsistencyGateToEventFlow x =
      registryExportConsistencyGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      registryExportConsistencyGateFromEventFlow
          (registryExportConsistencyGateToEventFlow x) =
        registryExportConsistencyGateFromEventFlow
          (registryExportConsistencyGateToEventFlow y) :=
    congrArg registryExportConsistencyGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (registryExportConsistencyGate_round_trip x).symm
      (Eq.trans hread (registryExportConsistencyGate_round_trip y)))

private theorem registryExportConsistencyGate_field_faithful :
    ∀ x y : RegistryExportConsistencyGateUp,
      registryExportConsistencyGateFields x =
        registryExportConsistencyGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk registry blocking status formalTarget audit noSmuggling transport replay provenance
      name =>
      cases y with
      | mk registry' blocking' status' formalTarget' audit' noSmuggling' transport' replay'
          provenance' name' =>
          cases hfields
          rfl

instance registryExportConsistencyGateBHistCarrier :
    BHistCarrier RegistryExportConsistencyGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := registryExportConsistencyGateToEventFlow
  fromEventFlow := registryExportConsistencyGateFromEventFlow

instance registryExportConsistencyGateChapterTasteGate :
    ChapterTasteGate RegistryExportConsistencyGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      registryExportConsistencyGateFromEventFlow
        (registryExportConsistencyGateToEventFlow x) = some x
    exact registryExportConsistencyGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (registryExportConsistencyGateToEventFlow_injective heq)

instance registryExportConsistencyGateFieldFaithful :
    FieldFaithful RegistryExportConsistencyGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := registryExportConsistencyGateFields
  field_faithful := registryExportConsistencyGate_field_faithful

instance registryExportConsistencyGateNontrivial :
    Nontrivial RegistryExportConsistencyGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegistryExportConsistencyGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegistryExportConsistencyGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegistryExportConsistencyGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  registryExportConsistencyGateChapterTasteGate

theorem RegistryExportConsistencyGateUp_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegistryExportConsistencyGateUp) ∧
      Nonempty (FieldFaithful RegistryExportConsistencyGateUp) ∧
        Nonempty (Nontrivial RegistryExportConsistencyGateUp) ∧
          (∃ x : RegistryExportConsistencyGateUp,
            FieldFaithful.fields x =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty]) ∧
            RegistryExportConsistencyGateUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty ≠
              RegistryExportConsistencyGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  refine ⟨⟨registryExportConsistencyGateChapterTasteGate⟩,
    ⟨registryExportConsistencyGateFieldFaithful⟩,
    ⟨registryExportConsistencyGateNontrivial⟩, ?_, ?_⟩
  · exact
      ⟨RegistryExportConsistencyGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩
  · intro h
    cases h

end BEDC.Derived.RegistryExportConsistencyGateUp
