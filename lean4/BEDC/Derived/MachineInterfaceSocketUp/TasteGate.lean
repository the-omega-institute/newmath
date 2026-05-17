import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineInterfaceSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineInterfaceSocketUp : Type where
  | root : MachineInterfaceSocketUp
  | mk :
      (target socketKind useLedger auditGate supplyLedger refusalLocality transport replay
        provenance localName : BHist) →
      MachineInterfaceSocketUp
  deriving DecidableEq

def machineInterfaceSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: machineInterfaceSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: machineInterfaceSocketEncodeBHist h

def machineInterfaceSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (machineInterfaceSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (machineInterfaceSocketDecodeBHist tail)

private theorem machineInterfaceSocketDecode_encode_bhist :
    ∀ h : BHist,
      machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem machineInterfaceSocket_mk_congr
    {target target' socketKind socketKind' useLedger useLedger' auditGate auditGate'
      supplyLedger supplyLedger' refusalLocality refusalLocality' transport transport'
      replay replay' provenance provenance' localName localName' : BHist}
    (hTarget : target' = target)
    (hSocketKind : socketKind' = socketKind)
    (hUseLedger : useLedger' = useLedger)
    (hAuditGate : auditGate' = auditGate)
    (hSupplyLedger : supplyLedger' = supplyLedger)
    (hRefusalLocality : refusalLocality' = refusalLocality)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    MachineInterfaceSocketUp.mk target' socketKind' useLedger' auditGate' supplyLedger'
        refusalLocality' transport' replay' provenance' localName' =
      MachineInterfaceSocketUp.mk target socketKind useLedger auditGate supplyLedger
        refusalLocality transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTarget
  cases hSocketKind
  cases hUseLedger
  cases hAuditGate
  cases hSupplyLedger
  cases hRefusalLocality
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def machineInterfaceSocketToEventFlow (x : MachineInterfaceSocketUp) : EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  match x with
  | MachineInterfaceSocketUp.root => [[BMark.b0]]
  | MachineInterfaceSocketUp.mk target socketKind useLedger auditGate supplyLedger
      refusalLocality transport replay provenance localName =>
      [[BMark.b1],
        machineInterfaceSocketEncodeBHist target,
        [BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist socketKind,
        [BMark.b1, BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist useLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist auditGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist supplyLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist refusalLocality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        machineInterfaceSocketEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        machineInterfaceSocketEncodeBHist localName]

def machineInterfaceSocketFromEventFlow :
    EventFlow → Option MachineInterfaceSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => some MachineInterfaceSocketUp.root
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | socketKind :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | useLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | supplyLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusalLocality :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MachineInterfaceSocketUp.mk
                                                                                          (machineInterfaceSocketDecodeBHist target)
                                                                                          (machineInterfaceSocketDecodeBHist socketKind)
                                                                                          (machineInterfaceSocketDecodeBHist useLedger)
                                                                                          (machineInterfaceSocketDecodeBHist auditGate)
                                                                                          (machineInterfaceSocketDecodeBHist supplyLedger)
                                                                                          (machineInterfaceSocketDecodeBHist refusalLocality)
                                                                                          (machineInterfaceSocketDecodeBHist transport)
                                                                                          (machineInterfaceSocketDecodeBHist replay)
                                                                                          (machineInterfaceSocketDecodeBHist provenance)
                                                                                          (machineInterfaceSocketDecodeBHist localName))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem machineInterfaceSocket_round_trip :
    ∀ x : MachineInterfaceSocketUp,
      machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | root =>
      rfl
  | mk target socketKind useLedger auditGate supplyLedger refusalLocality transport replay
      provenance localName =>
      change
        some
          (MachineInterfaceSocketUp.mk
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist target))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist socketKind))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist useLedger))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist auditGate))
            (machineInterfaceSocketDecodeBHist
              (machineInterfaceSocketEncodeBHist supplyLedger))
            (machineInterfaceSocketDecodeBHist
              (machineInterfaceSocketEncodeBHist refusalLocality))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist transport))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist replay))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist provenance))
            (machineInterfaceSocketDecodeBHist (machineInterfaceSocketEncodeBHist localName))) =
          some
            (MachineInterfaceSocketUp.mk target socketKind useLedger auditGate supplyLedger
              refusalLocality transport replay provenance localName)
      exact
        congrArg some
          (machineInterfaceSocket_mk_congr
            (machineInterfaceSocketDecode_encode_bhist target)
            (machineInterfaceSocketDecode_encode_bhist socketKind)
            (machineInterfaceSocketDecode_encode_bhist useLedger)
            (machineInterfaceSocketDecode_encode_bhist auditGate)
            (machineInterfaceSocketDecode_encode_bhist supplyLedger)
            (machineInterfaceSocketDecode_encode_bhist refusalLocality)
            (machineInterfaceSocketDecode_encode_bhist transport)
            (machineInterfaceSocketDecode_encode_bhist replay)
            (machineInterfaceSocketDecode_encode_bhist provenance)
            (machineInterfaceSocketDecode_encode_bhist localName))

private theorem machineInterfaceSocketToEventFlow_injective
    {x y : MachineInterfaceSocketUp} :
    machineInterfaceSocketToEventFlow x = machineInterfaceSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) =
        machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow y) :=
    congrArg machineInterfaceSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (machineInterfaceSocket_round_trip x).symm
      (Eq.trans hread (machineInterfaceSocket_round_trip y)))

instance machineInterfaceSocketBHistCarrier : BHistCarrier MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := machineInterfaceSocketToEventFlow
  fromEventFlow := machineInterfaceSocketFromEventFlow

instance machineInterfaceSocketChapterTasteGate :
    ChapterTasteGate MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      machineInterfaceSocketFromEventFlow (machineInterfaceSocketToEventFlow x) = some x
    exact machineInterfaceSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (machineInterfaceSocketToEventFlow_injective heq)

instance machineInterfaceSocketFieldFaithful : FieldFaithful MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MachineInterfaceSocketUp.root => []
    | MachineInterfaceSocketUp.mk target socketKind useLedger auditGate supplyLedger
        refusalLocality transport replay provenance localName =>
        [target, socketKind, useLedger, auditGate, supplyLedger, refusalLocality, transport,
          replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | root =>
        cases y with
        | root =>
            rfl
        | mk target₂ socketKind₂ useLedger₂ auditGate₂ supplyLedger₂ refusalLocality₂
            transport₂ replay₂ provenance₂ localName₂ =>
            cases h
    | mk target₁ socketKind₁ useLedger₁ auditGate₁ supplyLedger₁ refusalLocality₁
        transport₁ replay₁ provenance₁ localName₁ =>
        cases y with
        | root =>
            cases h
        | mk target₂ socketKind₂ useLedger₂ auditGate₂ supplyLedger₂ refusalLocality₂
            transport₂ replay₂ provenance₂ localName₂ =>
            simp only [] at h
            injection h with hTarget t1
            injection t1 with hSocketKind t2
            injection t2 with hUseLedger t3
            injection t3 with hAuditGate t4
            injection t4 with hSupplyLedger t5
            injection t5 with hRefusalLocality t6
            injection t6 with hTransport t7
            injection t7 with hReplay t8
            injection t8 with hProvenance t9
            injection t9 with hLocalName _
            subst hTarget
            subst hSocketKind
            subst hUseLedger
            subst hAuditGate
            subst hSupplyLedger
            subst hRefusalLocality
            subst hTransport
            subst hReplay
            subst hProvenance
            subst hLocalName
            rfl

instance machineInterfaceSocketNontrivial : Nontrivial MachineInterfaceSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := by
    exact
      ⟨MachineInterfaceSocketUp.root,
        MachineInterfaceSocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          cases h⟩

def taste_gate : ChapterTasteGate MachineInterfaceSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  machineInterfaceSocketChapterTasteGate

theorem MachineInterfaceSocketUp_taste_gate_obligations :
    Nonempty (ChapterTasteGate MachineInterfaceSocketUp) ∧
      Nonempty (FieldFaithful MachineInterfaceSocketUp) ∧
        ∃ x : MachineInterfaceSocketUp,
          BHistCarrier.toEventFlow x = [[BMark.b0]] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro machineInterfaceSocketChapterTasteGate,
      Nonempty.intro machineInterfaceSocketFieldFaithful,
      ⟨MachineInterfaceSocketUp.root,
        by
          rfl⟩⟩

end BEDC.Derived.MachineInterfaceSocketUp
