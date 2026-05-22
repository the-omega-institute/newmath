import BEDC.Derived.DenseUniformEmbeddingUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenseUniformEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def denseUniformEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denseUniformEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denseUniformEmbeddingEncodeBHist h

def denseUniformEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denseUniformEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denseUniformEmbeddingDecodeBHist tail)

private theorem denseUniformEmbedding_decode_encode_bhist :
    ∀ h : BHist,
      denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def denseUniformEmbeddingFields : DenseUniformEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenseUniformEmbeddingUp.mk S T I Q M E U H C P N => [S, T, I, Q, M, E, U, H, C, P, N]

def denseUniformEmbeddingToEventFlow : DenseUniformEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (denseUniformEmbeddingFields x).map denseUniformEmbeddingEncodeBHist

private def denseUniformEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => denseUniformEmbeddingEventAtDefault index rest

def denseUniformEmbeddingFromEventFlow (flow : EventFlow) :
    Option DenseUniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenseUniformEmbeddingUp.mk
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 0 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 1 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 2 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 3 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 4 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 5 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 6 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 7 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 8 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 9 flow))
      (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEventAtDefault 10 flow)))

private theorem denseUniformEmbedding_round_trip :
    ∀ x : DenseUniformEmbeddingUp,
      denseUniformEmbeddingFromEventFlow (denseUniformEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T I Q M E U H C P N =>
      change
        some
          (DenseUniformEmbeddingUp.mk
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist S))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist T))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist I))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist Q))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist M))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist E))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist U))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist H))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist C))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist P))
            (denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist N))) =
          some (DenseUniformEmbeddingUp.mk S T I Q M E U H C P N)
      rw [denseUniformEmbedding_decode_encode_bhist S,
        denseUniformEmbedding_decode_encode_bhist T, denseUniformEmbedding_decode_encode_bhist I,
        denseUniformEmbedding_decode_encode_bhist Q, denseUniformEmbedding_decode_encode_bhist M,
        denseUniformEmbedding_decode_encode_bhist E, denseUniformEmbedding_decode_encode_bhist U,
        denseUniformEmbedding_decode_encode_bhist H, denseUniformEmbedding_decode_encode_bhist C,
        denseUniformEmbedding_decode_encode_bhist P, denseUniformEmbedding_decode_encode_bhist N]

private theorem DenseUniformEmbeddingToEventFlow_injective {x y : DenseUniformEmbeddingUp} :
    denseUniformEmbeddingToEventFlow x = denseUniformEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denseUniformEmbeddingFromEventFlow (denseUniformEmbeddingToEventFlow x) =
        denseUniformEmbeddingFromEventFlow (denseUniformEmbeddingToEventFlow y) :=
    congrArg denseUniformEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (denseUniformEmbedding_round_trip x).symm
      (Eq.trans hread (denseUniformEmbedding_round_trip y)))

instance denseUniformEmbeddingBHistCarrier : BHistCarrier DenseUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denseUniformEmbeddingToEventFlow
  fromEventFlow := denseUniformEmbeddingFromEventFlow

instance denseUniformEmbeddingChapterTasteGate :
    ChapterTasteGate DenseUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denseUniformEmbeddingFromEventFlow (denseUniformEmbeddingToEventFlow x) = some x
    exact denseUniformEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DenseUniformEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DenseUniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denseUniformEmbeddingChapterTasteGate

theorem DenseUniformEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      denseUniformEmbeddingDecodeBHist (denseUniformEmbeddingEncodeBHist h) = h) ∧
      (∀ x : DenseUniformEmbeddingUp,
        denseUniformEmbeddingFromEventFlow (denseUniformEmbeddingToEventFlow x) = some x) ∧
        (∀ x y : DenseUniformEmbeddingUp,
          denseUniformEmbeddingToEventFlow x = denseUniformEmbeddingToEventFlow y → x = y) ∧
          denseUniformEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨denseUniformEmbedding_decode_encode_bhist, denseUniformEmbedding_round_trip,
      (fun _ _ heq => DenseUniformEmbeddingToEventFlow_injective heq), rfl⟩

end BEDC.Derived.DenseUniformEmbeddingUp
