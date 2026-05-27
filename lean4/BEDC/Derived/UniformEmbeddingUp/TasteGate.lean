import BEDC.Derived.UniformEmbeddingUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def uniformEmbeddingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformEmbeddingEncodeBHist h

def uniformEmbeddingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformEmbeddingDecodeBHist tail)

private theorem uniformEmbedding_decode_encode_bhist :
    forall h : BHist,
      uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformEmbeddingFields : UniformEmbeddingUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformEmbeddingUp.mk S T I U J R H C P N =>
      [S, T, I, U, J, R, H, C, P, N]

def uniformEmbeddingToEventFlow : UniformEmbeddingUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformEmbeddingFields x).map uniformEmbeddingEncodeBHist

private def uniformEmbeddingEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformEmbeddingEventAtDefault index rest

def uniformEmbeddingFromEventFlow
    (flow : EventFlow) : Option UniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformEmbeddingUp.mk
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 0 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 1 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 2 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 3 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 4 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 5 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 6 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 7 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 8 flow))
      (uniformEmbeddingDecodeBHist (uniformEmbeddingEventAtDefault 9 flow)))

private theorem uniformEmbedding_round_trip :
    forall x : UniformEmbeddingUp,
      uniformEmbeddingFromEventFlow (uniformEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T I U J R H C P N =>
      change
        some
          (UniformEmbeddingUp.mk
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist S))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist T))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist I))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist U))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist J))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist R))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist H))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist C))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist P))
            (uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist N))) =
          some (UniformEmbeddingUp.mk S T I U J R H C P N)
      rw [uniformEmbedding_decode_encode_bhist S,
        uniformEmbedding_decode_encode_bhist T,
        uniformEmbedding_decode_encode_bhist I,
        uniformEmbedding_decode_encode_bhist U,
        uniformEmbedding_decode_encode_bhist J,
        uniformEmbedding_decode_encode_bhist R,
        uniformEmbedding_decode_encode_bhist H,
        uniformEmbedding_decode_encode_bhist C,
        uniformEmbedding_decode_encode_bhist P,
        uniformEmbedding_decode_encode_bhist N]

private theorem UniformEmbeddingToEventFlow_injective {x y : UniformEmbeddingUp} :
    uniformEmbeddingToEventFlow x = uniformEmbeddingToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformEmbeddingFromEventFlow (uniformEmbeddingToEventFlow x) =
        uniformEmbeddingFromEventFlow (uniformEmbeddingToEventFlow y) :=
    congrArg uniformEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformEmbedding_round_trip x).symm
      (Eq.trans hread (uniformEmbedding_round_trip y)))

instance uniformEmbeddingBHistCarrier : BHistCarrier UniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformEmbeddingToEventFlow
  fromEventFlow := uniformEmbeddingFromEventFlow

instance uniformEmbeddingChapterTasteGate :
    ChapterTasteGate UniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformEmbeddingFromEventFlow (uniformEmbeddingToEventFlow x) = some x
    exact uniformEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformEmbeddingToEventFlow_injective heq)

theorem UniformEmbeddingTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformEmbeddingDecodeBHist (uniformEmbeddingEncodeBHist h) = h) /\
      (forall x : UniformEmbeddingUp,
        uniformEmbeddingFromEventFlow (uniformEmbeddingToEventFlow x) = some x) /\
        (forall x y : UniformEmbeddingUp,
          uniformEmbeddingToEventFlow x = uniformEmbeddingToEventFlow y -> x = y) /\
          uniformEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨uniformEmbedding_decode_encode_bhist, uniformEmbedding_round_trip,
      (fun _ _ heq => UniformEmbeddingToEventFlow_injective heq), rfl⟩

end BEDC.Derived.UniformEmbeddingUp
