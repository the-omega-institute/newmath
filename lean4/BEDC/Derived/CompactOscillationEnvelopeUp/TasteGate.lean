import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOscillationEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactOscillationEnvelopeUp : Type where
  | mk (K M F D R B U H C P N : BHist) : CompactOscillationEnvelopeUp
  deriving DecidableEq

def compactOscillationEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOscillationEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOscillationEnvelopeEncodeBHist h

def compactOscillationEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOscillationEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOscillationEnvelopeDecodeBHist tail)

private theorem compactOscillationEnvelope_decode_encode_bhist :
    ∀ h : BHist,
      compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactOscillationEnvelopeFields : CompactOscillationEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOscillationEnvelopeUp.mk K M F D R B U H C P N =>
      [K, M, F, D, R, B, U, H, C, P, N]

def compactOscillationEnvelopeToEventFlow : CompactOscillationEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactOscillationEnvelopeFields x).map compactOscillationEnvelopeEncodeBHist

private def compactOscillationEnvelopeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactOscillationEnvelopeEventAt index rest

def compactOscillationEnvelopeFromEventFlow
    (flow : EventFlow) : Option CompactOscillationEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactOscillationEnvelopeUp.mk
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 0 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 1 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 2 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 3 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 4 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 5 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 6 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 7 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 8 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 9 flow))
      (compactOscillationEnvelopeDecodeBHist (compactOscillationEnvelopeEventAt 10 flow)))

private theorem compactOscillationEnvelope_round_trip :
    ∀ x : CompactOscillationEnvelopeUp,
      compactOscillationEnvelopeFromEventFlow (compactOscillationEnvelopeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M F D R B U H C P N =>
      change
        some
            (CompactOscillationEnvelopeUp.mk
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist K))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist M))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist F))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist D))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist R))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist B))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist U))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist H))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist C))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist P))
              (compactOscillationEnvelopeDecodeBHist
                (compactOscillationEnvelopeEncodeBHist N))) =
          some (CompactOscillationEnvelopeUp.mk K M F D R B U H C P N)
      rw [compactOscillationEnvelope_decode_encode_bhist K,
        compactOscillationEnvelope_decode_encode_bhist M,
        compactOscillationEnvelope_decode_encode_bhist F,
        compactOscillationEnvelope_decode_encode_bhist D,
        compactOscillationEnvelope_decode_encode_bhist R,
        compactOscillationEnvelope_decode_encode_bhist B,
        compactOscillationEnvelope_decode_encode_bhist U,
        compactOscillationEnvelope_decode_encode_bhist H,
        compactOscillationEnvelope_decode_encode_bhist C,
        compactOscillationEnvelope_decode_encode_bhist P,
        compactOscillationEnvelope_decode_encode_bhist N]

private theorem compactOscillationEnvelopeToEventFlow_injective
    {x y : CompactOscillationEnvelopeUp} :
    compactOscillationEnvelopeToEventFlow x = compactOscillationEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactOscillationEnvelopeFromEventFlow (compactOscillationEnvelopeToEventFlow x) =
        compactOscillationEnvelopeFromEventFlow (compactOscillationEnvelopeToEventFlow y) :=
    congrArg compactOscillationEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactOscillationEnvelope_round_trip x).symm
      (Eq.trans hread (compactOscillationEnvelope_round_trip y)))

instance compactOscillationEnvelopeBHistCarrier :
    BHistCarrier CompactOscillationEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOscillationEnvelopeToEventFlow
  fromEventFlow := compactOscillationEnvelopeFromEventFlow

instance compactOscillationEnvelopeChapterTasteGate :
    ChapterTasteGate CompactOscillationEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactOscillationEnvelopeFromEventFlow (compactOscillationEnvelopeToEventFlow x) =
        some x
    exact compactOscillationEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactOscillationEnvelopeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactOscillationEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactOscillationEnvelopeChapterTasteGate

theorem CompactOscillationEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactOscillationEnvelopeUp) ∧
      Nonempty (ChapterTasteGate CompactOscillationEnvelopeUp) ∧
        (∀ h : BHist,
          compactOscillationEnvelopeDecodeBHist
              (compactOscillationEnvelopeEncodeBHist h) =
            h) ∧
          (∀ x : CompactOscillationEnvelopeUp,
            compactOscillationEnvelopeFromEventFlow
                (compactOscillationEnvelopeToEventFlow x) =
              some x) ∧
            compactOscillationEnvelopeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨compactOscillationEnvelopeBHistCarrier⟩
  constructor
  · exact ⟨compactOscillationEnvelopeChapterTasteGate⟩
  constructor
  · exact compactOscillationEnvelope_decode_encode_bhist
  constructor
  · exact compactOscillationEnvelope_round_trip
  · rfl

end BEDC.Derived.CompactOscillationEnvelopeUp
