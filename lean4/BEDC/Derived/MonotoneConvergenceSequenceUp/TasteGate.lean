import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneConvergenceSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneConvergenceSequenceUp : Type where
  | mk (S L U W D R E H C P N : BHist) : MonotoneConvergenceSequenceUp
  deriving DecidableEq

def monotoneConvergenceSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneConvergenceSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneConvergenceSequenceEncodeBHist h

def monotoneConvergenceSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneConvergenceSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneConvergenceSequenceDecodeBHist tail)

private theorem monotoneConvergenceSequence_decode_encode_bhist :
    ∀ h : BHist,
      monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneConvergenceSequenceFields :
    MonotoneConvergenceSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneConvergenceSequenceUp.mk S L U W D R E H C P N =>
      [S, L, U, W, D, R, E, H, C, P, N]

def monotoneConvergenceSequenceToEventFlow :
    MonotoneConvergenceSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (monotoneConvergenceSequenceFields x).map
      monotoneConvergenceSequenceEncodeBHist

private def monotoneConvergenceSequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      monotoneConvergenceSequenceRawAt index rest

def monotoneConvergenceSequenceFromEventFlow
    (flow : EventFlow) : Option MonotoneConvergenceSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneConvergenceSequenceUp.mk
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 0 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 1 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 2 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 3 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 4 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 5 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 6 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 7 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 8 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 9 flow))
      (monotoneConvergenceSequenceDecodeBHist
        (monotoneConvergenceSequenceRawAt 10 flow)))

private theorem monotoneConvergenceSequence_round_trip :
    ∀ x : MonotoneConvergenceSequenceUp,
      monotoneConvergenceSequenceFromEventFlow
        (monotoneConvergenceSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L U W D R E H C P N =>
      change
        some
          (MonotoneConvergenceSequenceUp.mk
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist S))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist L))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist U))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist W))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist D))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist R))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist E))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist H))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist C))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist P))
            (monotoneConvergenceSequenceDecodeBHist
              (monotoneConvergenceSequenceEncodeBHist N))) =
          some (MonotoneConvergenceSequenceUp.mk S L U W D R E H C P N)
      rw [monotoneConvergenceSequence_decode_encode_bhist S,
        monotoneConvergenceSequence_decode_encode_bhist L,
        monotoneConvergenceSequence_decode_encode_bhist U,
        monotoneConvergenceSequence_decode_encode_bhist W,
        monotoneConvergenceSequence_decode_encode_bhist D,
        monotoneConvergenceSequence_decode_encode_bhist R,
        monotoneConvergenceSequence_decode_encode_bhist E,
        monotoneConvergenceSequence_decode_encode_bhist H,
        monotoneConvergenceSequence_decode_encode_bhist C,
        monotoneConvergenceSequence_decode_encode_bhist P,
        monotoneConvergenceSequence_decode_encode_bhist N]

private theorem monotoneConvergenceSequenceToEventFlow_injective
    {x y : MonotoneConvergenceSequenceUp} :
    monotoneConvergenceSequenceToEventFlow x =
      monotoneConvergenceSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneConvergenceSequenceFromEventFlow
          (monotoneConvergenceSequenceToEventFlow x) =
        monotoneConvergenceSequenceFromEventFlow
          (monotoneConvergenceSequenceToEventFlow y) :=
    congrArg monotoneConvergenceSequenceFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (monotoneConvergenceSequence_round_trip x).symm
        (Eq.trans hread (monotoneConvergenceSequence_round_trip y)))

private theorem monotoneConvergenceSequence_field_faithful :
    ∀ x y : MonotoneConvergenceSequenceUp,
      monotoneConvergenceSequenceFields x =
        monotoneConvergenceSequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance monotoneConvergenceSequenceBHistCarrier :
    BHistCarrier MonotoneConvergenceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneConvergenceSequenceToEventFlow
  fromEventFlow := monotoneConvergenceSequenceFromEventFlow

instance monotoneConvergenceSequenceChapterTasteGate :
    ChapterTasteGate MonotoneConvergenceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneConvergenceSequenceFromEventFlow
        (monotoneConvergenceSequenceToEventFlow x) = some x
    exact monotoneConvergenceSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneConvergenceSequenceToEventFlow_injective heq)

instance monotoneConvergenceSequenceFieldFaithful :
    FieldFaithful MonotoneConvergenceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monotoneConvergenceSequenceFields
  field_faithful := monotoneConvergenceSequence_field_faithful

instance monotoneConvergenceSequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MonotoneConvergenceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MonotoneConvergenceSequenceUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MonotoneConvergenceSequenceUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MonotoneConvergenceSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneConvergenceSequenceChapterTasteGate

theorem MonotoneConvergenceSequenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier MonotoneConvergenceSequenceUp) ∧
      Nonempty (ChapterTasteGate MonotoneConvergenceSequenceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial MonotoneConvergenceSequenceUp) ∧
      (∀ h : BHist,
        monotoneConvergenceSequenceDecodeBHist
          (monotoneConvergenceSequenceEncodeBHist h) = h) ∧
      (∀ x : MonotoneConvergenceSequenceUp,
        monotoneConvergenceSequenceFromEventFlow
          (monotoneConvergenceSequenceToEventFlow x) = some x) ∧
      (∀ x y : MonotoneConvergenceSequenceUp,
        monotoneConvergenceSequenceToEventFlow x =
          monotoneConvergenceSequenceToEventFlow y → x = y) ∧
      monotoneConvergenceSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨monotoneConvergenceSequenceBHistCarrier⟩,
      ⟨monotoneConvergenceSequenceChapterTasteGate⟩,
      ⟨monotoneConvergenceSequenceNontrivial⟩,
      monotoneConvergenceSequence_decode_encode_bhist,
      monotoneConvergenceSequence_round_trip,
      (fun _ _ heq => monotoneConvergenceSequenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MonotoneConvergenceSequenceUp
