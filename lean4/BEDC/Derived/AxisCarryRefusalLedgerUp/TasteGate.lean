import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisCarryRefusalLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisCarryRefusalLedgerUp : Type where
  | mk :
      (registry carryRefusal fullAxisRefusal axisNatRefusal bridgeBoundary ledger transport
        replay provenance localName : BHist) →
        AxisCarryRefusalLedgerUp
  deriving DecidableEq

def axisCarryRefusalLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisCarryRefusalLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisCarryRefusalLedgerEncodeBHist h

def axisCarryRefusalLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisCarryRefusalLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisCarryRefusalLedgerDecodeBHist tail)

private theorem axisCarryRefusalLedger_decode_encode_bhist :
    ∀ h : BHist,
      axisCarryRefusalLedgerDecodeBHist (axisCarryRefusalLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisCarryRefusalLedgerToEventFlow : AxisCarryRefusalLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryRefusalLedgerUp.mk registry carryRefusal fullAxisRefusal axisNatRefusal
      bridgeBoundary ledger transport replay provenance localName =>
      [[BMark.b0],
        axisCarryRefusalLedgerEncodeBHist registry,
        [BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist carryRefusal,
        [BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist fullAxisRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist axisNatRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist bridgeBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisCarryRefusalLedgerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist localName]

def axisCarryRefusalLedgerFromEventFlow : EventFlow → Option AxisCarryRefusalLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | registry :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | carryRefusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | fullAxisRefusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | axisNatRefusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | bridgeBoundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
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
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (AxisCarryRefusalLedgerUp.mk
                                                                                          (axisCarryRefusalLedgerDecodeBHist registry)
                                                                                          (axisCarryRefusalLedgerDecodeBHist carryRefusal)
                                                                                          (axisCarryRefusalLedgerDecodeBHist fullAxisRefusal)
                                                                                          (axisCarryRefusalLedgerDecodeBHist axisNatRefusal)
                                                                                          (axisCarryRefusalLedgerDecodeBHist bridgeBoundary)
                                                                                          (axisCarryRefusalLedgerDecodeBHist ledger)
                                                                                          (axisCarryRefusalLedgerDecodeBHist transport)
                                                                                          (axisCarryRefusalLedgerDecodeBHist replay)
                                                                                          (axisCarryRefusalLedgerDecodeBHist provenance)
                                                                                          (axisCarryRefusalLedgerDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem axisCarryRefusalLedger_round_trip :
    ∀ x : AxisCarryRefusalLedgerUp,
      axisCarryRefusalLedgerFromEventFlow
        (axisCarryRefusalLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk registry carryRefusal fullAxisRefusal axisNatRefusal bridgeBoundary ledger transport
      replay provenance localName =>
      change
        some
          (AxisCarryRefusalLedgerUp.mk
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist registry))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist carryRefusal))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist fullAxisRefusal))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist axisNatRefusal))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist bridgeBoundary))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist ledger))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist transport))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist replay))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist provenance))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist localName))) =
          some
            (AxisCarryRefusalLedgerUp.mk registry carryRefusal fullAxisRefusal
              axisNatRefusal bridgeBoundary ledger transport replay provenance localName)
      rw [axisCarryRefusalLedger_decode_encode_bhist registry,
        axisCarryRefusalLedger_decode_encode_bhist carryRefusal,
        axisCarryRefusalLedger_decode_encode_bhist fullAxisRefusal,
        axisCarryRefusalLedger_decode_encode_bhist axisNatRefusal,
        axisCarryRefusalLedger_decode_encode_bhist bridgeBoundary,
        axisCarryRefusalLedger_decode_encode_bhist ledger,
        axisCarryRefusalLedger_decode_encode_bhist transport,
        axisCarryRefusalLedger_decode_encode_bhist replay,
        axisCarryRefusalLedger_decode_encode_bhist provenance,
        axisCarryRefusalLedger_decode_encode_bhist localName]

private theorem axisCarryRefusalLedgerToEventFlow_injective
    {x y : AxisCarryRefusalLedgerUp} :
    axisCarryRefusalLedgerToEventFlow x =
      axisCarryRefusalLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisCarryRefusalLedgerFromEventFlow
          (axisCarryRefusalLedgerToEventFlow x) =
        axisCarryRefusalLedgerFromEventFlow
          (axisCarryRefusalLedgerToEventFlow y) :=
    congrArg axisCarryRefusalLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisCarryRefusalLedger_round_trip x).symm
      (Eq.trans hread (axisCarryRefusalLedger_round_trip y)))

private def axisCarryRefusalLedgerFields : AxisCarryRefusalLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryRefusalLedgerUp.mk registry carryRefusal fullAxisRefusal axisNatRefusal
      bridgeBoundary ledger transport replay provenance localName =>
      [registry, carryRefusal, fullAxisRefusal, axisNatRefusal, bridgeBoundary, ledger,
        transport, replay, provenance, localName]

private theorem axisCarryRefusalLedger_field_faithful :
    ∀ x y : AxisCarryRefusalLedgerUp,
      axisCarryRefusalLedgerFields x = axisCarryRefusalLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk registry carryRefusal fullAxisRefusal axisNatRefusal bridgeBoundary ledger transport
      replay provenance localName =>
      cases y with
      | mk registry' carryRefusal' fullAxisRefusal' axisNatRefusal' bridgeBoundary' ledger'
          transport' replay' provenance' localName' =>
          cases hfields
          rfl

instance axisCarryRefusalLedgerBHistCarrier :
    BHistCarrier AxisCarryRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisCarryRefusalLedgerToEventFlow
  fromEventFlow := axisCarryRefusalLedgerFromEventFlow

instance axisCarryRefusalLedgerChapterTasteGate :
    ChapterTasteGate AxisCarryRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      axisCarryRefusalLedgerFromEventFlow
        (axisCarryRefusalLedgerToEventFlow x) = some x
    exact axisCarryRefusalLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisCarryRefusalLedgerToEventFlow_injective heq)

instance axisCarryRefusalLedgerFieldFaithful :
    FieldFaithful AxisCarryRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axisCarryRefusalLedgerFields
  field_faithful := axisCarryRefusalLedger_field_faithful

instance axisCarryRefusalLedgerNontrivial :
    Nontrivial AxisCarryRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisCarryRefusalLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisCarryRefusalLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisCarryRefusalLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisCarryRefusalLedgerChapterTasteGate

theorem AxisCarryRefusalLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      axisCarryRefusalLedgerDecodeBHist (axisCarryRefusalLedgerEncodeBHist h) = h) ∧
      (∀ x : AxisCarryRefusalLedgerUp,
        axisCarryRefusalLedgerFromEventFlow
          (axisCarryRefusalLedgerToEventFlow x) = some x) ∧
        (∀ x y : AxisCarryRefusalLedgerUp,
          axisCarryRefusalLedgerToEventFlow x =
            axisCarryRefusalLedgerToEventFlow y → x = y) ∧
          axisCarryRefusalLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact axisCarryRefusalLedger_decode_encode_bhist h
  · constructor
    · intro x
      exact axisCarryRefusalLedger_round_trip x
    · constructor
      · intro x y heq
        exact axisCarryRefusalLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AxisCarryRefusalLedgerUp.TasteGate
