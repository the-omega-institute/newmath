import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegistryConsistencyAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegistryConsistencyAuditUp : Type where
  | mk :
      (registry status dependency gap cannotClaim formal proofTrace transport replay
        provenance name : BHist) →
      RegistryConsistencyAuditUp
  deriving DecidableEq

def registryConsistencyAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: registryConsistencyAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: registryConsistencyAuditEncodeBHist h

def registryConsistencyAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (registryConsistencyAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (registryConsistencyAuditDecodeBHist tail)

private theorem registryConsistencyAudit_decode_encode_bhist :
    ∀ h : BHist,
      registryConsistencyAuditDecodeBHist (registryConsistencyAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem registryConsistencyAudit_mk_congr
    {registry registry' status status' dependency dependency' gap gap'
      cannotClaim cannotClaim' formal formal' proofTrace proofTrace' transport transport'
      replay replay' provenance provenance' name name' : BHist}
    (hregistry : registry' = registry)
    (hstatus : status' = status)
    (hdependency : dependency' = dependency)
    (hgap : gap' = gap)
    (hcannotClaim : cannotClaim' = cannotClaim)
    (hformal : formal' = formal)
    (hproofTrace : proofTrace' = proofTrace)
    (htransport : transport' = transport)
    (hreplay : replay' = replay)
    (hprovenance : provenance' = provenance)
    (hname : name' = name) :
    RegistryConsistencyAuditUp.mk registry' status' dependency' gap' cannotClaim' formal'
        proofTrace' transport' replay' provenance' name' =
      RegistryConsistencyAuditUp.mk registry status dependency gap cannotClaim formal proofTrace
        transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hregistry
  cases hstatus
  cases hdependency
  cases hgap
  cases hcannotClaim
  cases hformal
  cases hproofTrace
  cases htransport
  cases hreplay
  cases hprovenance
  cases hname
  rfl

def registryConsistencyAuditFields : RegistryConsistencyAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryConsistencyAuditUp.mk registry status dependency gap cannotClaim formal proofTrace
      transport replay provenance name =>
      [registry, status, dependency, gap, cannotClaim, formal, proofTrace, transport, replay,
        provenance, name]

def registryConsistencyAuditToEventFlow : RegistryConsistencyAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryConsistencyAuditUp.mk registry status dependency gap cannotClaim formal proofTrace
      transport replay provenance name =>
      [[BMark.b0], registryConsistencyAuditEncodeBHist registry,
        [BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist status,
        [BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist dependency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist formal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist proofTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        registryConsistencyAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryConsistencyAuditEncodeBHist name]

private def registryConsistencyAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => registryConsistencyAuditEventAtDefault index rest

def registryConsistencyAuditFromEventFlow (ef : EventFlow) :
    Option RegistryConsistencyAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegistryConsistencyAuditUp.mk
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 1 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 3 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 5 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 7 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 9 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 11 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 13 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 15 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 17 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 19 ef))
      (registryConsistencyAuditDecodeBHist (registryConsistencyAuditEventAtDefault 21 ef)))

private theorem registryConsistencyAudit_round_trip :
    ∀ x : RegistryConsistencyAuditUp,
      registryConsistencyAuditFromEventFlow (registryConsistencyAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk registry status dependency gap cannotClaim formal proofTrace transport replay provenance
      name =>
      change
        some
          (RegistryConsistencyAuditUp.mk
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist registry))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist status))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist dependency))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist gap))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist cannotClaim))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist formal))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist proofTrace))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist transport))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist replay))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist provenance))
            (registryConsistencyAuditDecodeBHist
              (registryConsistencyAuditEncodeBHist name))) =
          some
            (RegistryConsistencyAuditUp.mk registry status dependency gap cannotClaim formal
              proofTrace transport replay provenance name)
      exact
        congrArg some
          (registryConsistencyAudit_mk_congr
            (registryConsistencyAudit_decode_encode_bhist registry)
            (registryConsistencyAudit_decode_encode_bhist status)
            (registryConsistencyAudit_decode_encode_bhist dependency)
            (registryConsistencyAudit_decode_encode_bhist gap)
            (registryConsistencyAudit_decode_encode_bhist cannotClaim)
            (registryConsistencyAudit_decode_encode_bhist formal)
            (registryConsistencyAudit_decode_encode_bhist proofTrace)
            (registryConsistencyAudit_decode_encode_bhist transport)
            (registryConsistencyAudit_decode_encode_bhist replay)
            (registryConsistencyAudit_decode_encode_bhist provenance)
            (registryConsistencyAudit_decode_encode_bhist name))

private theorem registryConsistencyAuditToEventFlow_injective
    {x y : RegistryConsistencyAuditUp} :
    registryConsistencyAuditToEventFlow x = registryConsistencyAuditToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      registryConsistencyAuditFromEventFlow (registryConsistencyAuditToEventFlow x) =
        registryConsistencyAuditFromEventFlow (registryConsistencyAuditToEventFlow y) :=
    congrArg registryConsistencyAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (registryConsistencyAudit_round_trip x).symm
      (Eq.trans hread (registryConsistencyAudit_round_trip y)))

private theorem registryConsistencyAudit_field_faithful :
    ∀ x y : RegistryConsistencyAuditUp,
      registryConsistencyAuditFields x = registryConsistencyAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk registry₁ status₁ dependency₁ gap₁ cannotClaim₁ formal₁ proofTrace₁ transport₁
      replay₁ provenance₁ name₁ =>
      cases y with
      | mk registry₂ status₂ dependency₂ gap₂ cannotClaim₂ formal₂ proofTrace₂ transport₂
          replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance registryConsistencyAuditBHistCarrier :
    BHistCarrier RegistryConsistencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := registryConsistencyAuditToEventFlow
  fromEventFlow := registryConsistencyAuditFromEventFlow

instance registryConsistencyAuditChapterTasteGate :
    ChapterTasteGate RegistryConsistencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      registryConsistencyAuditFromEventFlow (registryConsistencyAuditToEventFlow x) =
        some x
    exact registryConsistencyAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (registryConsistencyAuditToEventFlow_injective heq)

instance registryConsistencyAuditFieldFaithful :
    FieldFaithful RegistryConsistencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := registryConsistencyAuditFields
  field_faithful := registryConsistencyAudit_field_faithful

instance registryConsistencyAuditNontrivial : Nontrivial RegistryConsistencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegistryConsistencyAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegistryConsistencyAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegistryConsistencyAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  registryConsistencyAuditChapterTasteGate

theorem RegistryConsistencyAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        registryConsistencyAuditDecodeBHist (registryConsistencyAuditEncodeBHist h) = h) ∧
      (∀ x : RegistryConsistencyAuditUp,
        registryConsistencyAuditFromEventFlow (registryConsistencyAuditToEventFlow x) =
          some x) ∧
      (∀ x y : RegistryConsistencyAuditUp,
        registryConsistencyAuditToEventFlow x = registryConsistencyAuditToEventFlow y →
          x = y) ∧
      registryConsistencyAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨registryConsistencyAudit_decode_encode_bhist, registryConsistencyAudit_round_trip,
      (by
        intro x y heq
        exact registryConsistencyAuditToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegistryConsistencyAuditUp
