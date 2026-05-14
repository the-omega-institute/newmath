import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxiomRefusalLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxiomRefusalLedgerUp : Type where
  | mk :
      (name socket question alternative refusal readback transport route provenance localName :
        BHist) →
        AxiomRefusalLedgerUp
  deriving DecidableEq

def axiomRefusalLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axiomRefusalLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axiomRefusalLedgerEncodeBHist h

def axiomRefusalLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axiomRefusalLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axiomRefusalLedgerDecodeBHist tail)

private theorem axiomRefusalLedgerDecode_encode_bhist :
    ∀ h : BHist, axiomRefusalLedgerDecodeBHist
      (axiomRefusalLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axiomRefusalLedgerToEventFlow : AxiomRefusalLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomRefusalLedgerUp.mk name socket question alternative refusal readback transport route
      provenance localName =>
      [[BMark.b0],
        axiomRefusalLedgerEncodeBHist name,
        [BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist socket,
        [BMark.b1, BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist question,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist alternative,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axiomRefusalLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axiomRefusalLedgerEncodeBHist localName]

def axiomRefusalLedgerFromEventFlow : EventFlow → Option AxiomRefusalLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | name :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | socket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | question :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | alternative :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | readback :: rest11 =>
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
                                                              | route :: rest15 =>
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
                                                                                        (AxiomRefusalLedgerUp.mk
                                                                                          (axiomRefusalLedgerDecodeBHist name)
                                                                                          (axiomRefusalLedgerDecodeBHist socket)
                                                                                          (axiomRefusalLedgerDecodeBHist question)
                                                                                          (axiomRefusalLedgerDecodeBHist alternative)
                                                                                          (axiomRefusalLedgerDecodeBHist refusal)
                                                                                          (axiomRefusalLedgerDecodeBHist readback)
                                                                                          (axiomRefusalLedgerDecodeBHist transport)
                                                                                          (axiomRefusalLedgerDecodeBHist route)
                                                                                          (axiomRefusalLedgerDecodeBHist provenance)
                                                                                          (axiomRefusalLedgerDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem axiomRefusalLedger_round_trip :
    ∀ x : AxiomRefusalLedgerUp,
      axiomRefusalLedgerFromEventFlow (axiomRefusalLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk name socket question alternative refusal readback transport route provenance localName =>
      change
        some
          (AxiomRefusalLedgerUp.mk
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist name))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist socket))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist question))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist alternative))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist refusal))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist readback))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist transport))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist route))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist provenance))
            (axiomRefusalLedgerDecodeBHist (axiomRefusalLedgerEncodeBHist localName))) =
          some
            (AxiomRefusalLedgerUp.mk name socket question alternative refusal readback transport
              route provenance localName)
      rw [axiomRefusalLedgerDecode_encode_bhist name,
        axiomRefusalLedgerDecode_encode_bhist socket,
        axiomRefusalLedgerDecode_encode_bhist question,
        axiomRefusalLedgerDecode_encode_bhist alternative,
        axiomRefusalLedgerDecode_encode_bhist refusal,
        axiomRefusalLedgerDecode_encode_bhist readback,
        axiomRefusalLedgerDecode_encode_bhist transport,
        axiomRefusalLedgerDecode_encode_bhist route,
        axiomRefusalLedgerDecode_encode_bhist provenance,
        axiomRefusalLedgerDecode_encode_bhist localName]

private theorem axiomRefusalLedgerToEventFlow_injective {x y : AxiomRefusalLedgerUp} :
    axiomRefusalLedgerToEventFlow x = axiomRefusalLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axiomRefusalLedgerFromEventFlow (axiomRefusalLedgerToEventFlow x) =
        axiomRefusalLedgerFromEventFlow (axiomRefusalLedgerToEventFlow y) :=
    congrArg axiomRefusalLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axiomRefusalLedger_round_trip x).symm
      (Eq.trans hread (axiomRefusalLedger_round_trip y)))

instance axiomRefusalLedgerBHistCarrier : BHistCarrier AxiomRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axiomRefusalLedgerToEventFlow
  fromEventFlow := axiomRefusalLedgerFromEventFlow

instance axiomRefusalLedgerChapterTasteGate : ChapterTasteGate AxiomRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axiomRefusalLedgerFromEventFlow (axiomRefusalLedgerToEventFlow x) = some x
    exact axiomRefusalLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axiomRefusalLedgerToEventFlow_injective heq)

instance axiomRefusalLedgerFieldFaithful : FieldFaithful AxiomRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AxiomRefusalLedgerUp.mk name socket question alternative refusal readback transport route
        provenance localName =>
        [name, socket, question, alternative, refusal, readback, transport, route, provenance,
          localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk name1 socket1 question1 alternative1 refusal1 readback1 transport1 route1 provenance1
        localName1 =>
        cases y with
        | mk name2 socket2 question2 alternative2 refusal2 readback2 transport2 route2 provenance2
            localName2 =>
            cases h
            rfl

instance axiomRefusalLedgerNontrivial : Nontrivial AxiomRefusalLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxiomRefusalLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxiomRefusalLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxiomRefusalLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axiomRefusalLedgerChapterTasteGate

theorem AxiomRefusalLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AxiomRefusalLedgerUp) ∧
      (∀ x : AxiomRefusalLedgerUp,
        axiomRefusalLedgerFromEventFlow (axiomRefusalLedgerToEventFlow x) = some x) ∧
      (∀ x y : AxiomRefusalLedgerUp,
        axiomRefusalLedgerToEventFlow x = axiomRefusalLedgerToEventFlow y → x = y) ∧
      axiomRefusalLedgerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨axiomRefusalLedgerChapterTasteGate⟩
  · constructor
    · intro x
      change axiomRefusalLedgerFromEventFlow (axiomRefusalLedgerToEventFlow x) = some x
      exact axiomRefusalLedger_round_trip x
    · constructor
      · intro x y heq
        exact axiomRefusalLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AxiomRefusalLedgerUp
