import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WitnessedDescentLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WitnessedDescentLedgerUp : Type where
  | mk (source bridge descentRequest witness transport continuation provenance name : BHist) :
      WitnessedDescentLedgerUp

private def witnessedDescentLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: witnessedDescentLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: witnessedDescentLedgerEncodeBHist h

private def witnessedDescentLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (witnessedDescentLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (witnessedDescentLedgerDecodeBHist tail)

private theorem witnessedDescentLedger_decode_encode_bhist :
    ∀ h : BHist,
      witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def witnessedDescentLedgerToEventFlow : WitnessedDescentLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport continuation
      provenance name =>
      [[BMark.b0],
        witnessedDescentLedgerEncodeBHist source,
        [BMark.b1, BMark.b0],
        witnessedDescentLedgerEncodeBHist bridge,
        [BMark.b1, BMark.b1, BMark.b0],
        witnessedDescentLedgerEncodeBHist descentRequest,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedDescentLedgerEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedDescentLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedDescentLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        witnessedDescentLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        witnessedDescentLedgerEncodeBHist name]

private def witnessedDescentLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => witnessedDescentLedgerRawAt n rest

private def witnessedDescentLedgerLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => witnessedDescentLedgerLengthEq n rest

private def witnessedDescentLedgerFromEventFlow : EventFlow → Option WitnessedDescentLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match witnessedDescentLedgerLengthEq 16 flow with
      | true =>
          some
            (WitnessedDescentLedgerUp.mk
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 1 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 3 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 5 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 7 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 9 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 11 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 13 flow))
              (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerRawAt 15 flow)))
      | false => none

private theorem witnessedDescentLedger_round_trip :
    ∀ x : WitnessedDescentLedgerUp,
      witnessedDescentLedgerFromEventFlow (witnessedDescentLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source bridge descentRequest witness transport continuation provenance name =>
      change
        some
          (WitnessedDescentLedgerUp.mk
            (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist source))
            (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist bridge))
            (witnessedDescentLedgerDecodeBHist
              (witnessedDescentLedgerEncodeBHist descentRequest))
            (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist witness))
            (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist transport))
            (witnessedDescentLedgerDecodeBHist
              (witnessedDescentLedgerEncodeBHist continuation))
            (witnessedDescentLedgerDecodeBHist
              (witnessedDescentLedgerEncodeBHist provenance))
            (witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist name))) =
          some
            (WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport
              continuation provenance name)
      rw [witnessedDescentLedger_decode_encode_bhist source,
        witnessedDescentLedger_decode_encode_bhist bridge,
        witnessedDescentLedger_decode_encode_bhist descentRequest,
        witnessedDescentLedger_decode_encode_bhist witness,
        witnessedDescentLedger_decode_encode_bhist transport,
        witnessedDescentLedger_decode_encode_bhist continuation,
        witnessedDescentLedger_decode_encode_bhist provenance,
        witnessedDescentLedger_decode_encode_bhist name]

private theorem witnessedDescentLedgerToEventFlow_injective {x y : WitnessedDescentLedgerUp} :
    witnessedDescentLedgerToEventFlow x = witnessedDescentLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      witnessedDescentLedgerFromEventFlow (witnessedDescentLedgerToEventFlow x) =
        witnessedDescentLedgerFromEventFlow (witnessedDescentLedgerToEventFlow y) :=
    congrArg witnessedDescentLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (witnessedDescentLedger_round_trip x).symm
      (Eq.trans hread (witnessedDescentLedger_round_trip y)))

private def witnessedDescentLedgerFields : WitnessedDescentLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport continuation
      provenance name =>
      [source, bridge, descentRequest, witness, transport, continuation, provenance, name]

private theorem witnessedDescentLedger_field_faithful :
    ∀ x y : WitnessedDescentLedgerUp,
      witnessedDescentLedgerFields x = witnessedDescentLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ bridge₁ descentRequest₁ witness₁ transport₁ continuation₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ bridge₂ descentRequest₂ witness₂ transport₂ continuation₂ provenance₂ name₂ =>
          cases h
          rfl

instance witnessedDescentLedgerBHistCarrier : BHistCarrier WitnessedDescentLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := witnessedDescentLedgerToEventFlow
  fromEventFlow := witnessedDescentLedgerFromEventFlow

instance witnessedDescentLedgerChapterTasteGate : ChapterTasteGate WitnessedDescentLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change witnessedDescentLedgerFromEventFlow (witnessedDescentLedgerToEventFlow x) = some x
    exact witnessedDescentLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (witnessedDescentLedgerToEventFlow_injective heq)

instance witnessedDescentLedgerFieldFaithful : FieldFaithful WitnessedDescentLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := witnessedDescentLedgerFields
  field_faithful := witnessedDescentLedger_field_faithful

instance witnessedDescentLedgerNontrivial : Nontrivial WitnessedDescentLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WitnessedDescentLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WitnessedDescentLedgerUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WitnessedDescentLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  witnessedDescentLedgerChapterTasteGate

theorem WitnessedDescentLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      witnessedDescentLedgerDecodeBHist (witnessedDescentLedgerEncodeBHist h) = h) ∧
      (∀ x : WitnessedDescentLedgerUp,
        witnessedDescentLedgerFromEventFlow (witnessedDescentLedgerToEventFlow x) = some x) ∧
        (∀ x y : WitnessedDescentLedgerUp,
          witnessedDescentLedgerToEventFlow x = witnessedDescentLedgerToEventFlow y → x = y) ∧
          witnessedDescentLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨witnessedDescentLedger_decode_encode_bhist,
      witnessedDescentLedger_round_trip,
      by
        intro x y heq
        exact witnessedDescentLedgerToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.WitnessedDescentLedgerUp
