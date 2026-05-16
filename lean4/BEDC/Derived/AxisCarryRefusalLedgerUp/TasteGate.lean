import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisCarryRefusalLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisCarryRefusalLedgerUp : Type where
  | mk :
      (registry carryRefusal fullAxisRefusal axisNatRefusal bridgeBoundary refusalLedger
        componentTransport continuationReplay provenance localName : BHist) →
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

private theorem axisCarryRefusalLedgerDecode_encode_bhist :
    ∀ h : BHist,
      axisCarryRefusalLedgerDecodeBHist
        (axisCarryRefusalLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisCarryRefusalLedgerToEventFlow :
    AxisCarryRefusalLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryRefusalLedgerUp.mk registry carryRefusal fullAxisRefusal axisNatRefusal
      bridgeBoundary refusalLedger componentTransport continuationReplay provenance localName =>
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
        axisCarryRefusalLedgerEncodeBHist refusalLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist componentTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisCarryRefusalLedgerEncodeBHist continuationReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axisCarryRefusalLedgerEncodeBHist localName]

def axisCarryRefusalLedgerFromEventFlow :
    EventFlow → Option AxisCarryRefusalLedgerUp
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
                                              | refusalLedger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | componentTransport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuationReplay :: rest15 =>
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
                                                                                          (axisCarryRefusalLedgerDecodeBHist refusalLedger)
                                                                                          (axisCarryRefusalLedgerDecodeBHist componentTransport)
                                                                                          (axisCarryRefusalLedgerDecodeBHist continuationReplay)
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
  | mk registry carryRefusal fullAxisRefusal axisNatRefusal bridgeBoundary refusalLedger
      componentTransport continuationReplay provenance localName =>
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
              (axisCarryRefusalLedgerEncodeBHist refusalLedger))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist componentTransport))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist continuationReplay))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist provenance))
            (axisCarryRefusalLedgerDecodeBHist
              (axisCarryRefusalLedgerEncodeBHist localName))) =
          some
            (AxisCarryRefusalLedgerUp.mk registry carryRefusal fullAxisRefusal axisNatRefusal
              bridgeBoundary refusalLedger componentTransport continuationReplay provenance
              localName)
      rw [axisCarryRefusalLedgerDecode_encode_bhist registry,
        axisCarryRefusalLedgerDecode_encode_bhist carryRefusal,
        axisCarryRefusalLedgerDecode_encode_bhist fullAxisRefusal,
        axisCarryRefusalLedgerDecode_encode_bhist axisNatRefusal,
        axisCarryRefusalLedgerDecode_encode_bhist bridgeBoundary,
        axisCarryRefusalLedgerDecode_encode_bhist refusalLedger,
        axisCarryRefusalLedgerDecode_encode_bhist componentTransport,
        axisCarryRefusalLedgerDecode_encode_bhist continuationReplay,
        axisCarryRefusalLedgerDecode_encode_bhist provenance,
        axisCarryRefusalLedgerDecode_encode_bhist localName]

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
  fields := fun x =>
    match x with
    | AxisCarryRefusalLedgerUp.mk registry carryRefusal fullAxisRefusal axisNatRefusal
        bridgeBoundary refusalLedger componentTransport continuationReplay provenance
        localName =>
        [registry, carryRefusal, fullAxisRefusal, axisNatRefusal, bridgeBoundary,
          refusalLedger, componentTransport, continuationReplay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk registry1 carryRefusal1 fullAxisRefusal1 axisNatRefusal1 bridgeBoundary1
        refusalLedger1 componentTransport1 continuationReplay1 provenance1 localName1 =>
        cases y with
        | mk registry2 carryRefusal2 fullAxisRefusal2 axisNatRefusal2 bridgeBoundary2
            refusalLedger2 componentTransport2 continuationReplay2 provenance2 localName2 =>
            cases h
            rfl

instance axisCarryRefusalLedgerNontrivial :
    Nontrivial AxisCarryRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisCarryRefusalLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxisCarryRefusalLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisCarryRefusalLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisCarryRefusalLedgerChapterTasteGate

theorem AxisCarryRefusalLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      axisCarryRefusalLedgerDecodeBHist
        (axisCarryRefusalLedgerEncodeBHist h) = h) ∧
      (axisCarryRefusalLedgerToEventFlow
          (AxisCarryRefusalLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
        axisCarryRefusalLedgerToEventFlow
          (AxisCarryRefusalLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty)) ∧
      (∀ x : AxisCarryRefusalLedgerUp,
        axisCarryRefusalLedgerFromEventFlow (axisCarryRefusalLedgerToEventFlow x) = some x) ∧
      Nonempty (Nontrivial AxisCarryRefusalLedgerUp) ∧
        Nonempty (FieldFaithful AxisCarryRefusalLedgerUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact axisCarryRefusalLedgerDecode_encode_bhist
  · constructor
    · intro heq
      have hsame :
          AxisCarryRefusalLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty =
            AxisCarryRefusalLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty :=
        axisCarryRefusalLedgerToEventFlow_injective heq
      cases hsame
    · constructor
      · exact axisCarryRefusalLedger_round_trip
      · constructor
        · exact ⟨axisCarryRefusalLedgerNontrivial⟩
        · exact ⟨axisCarryRefusalLedgerFieldFaithful⟩

end BEDC.Derived.AxisCarryRefusalLedgerUp
