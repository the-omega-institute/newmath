import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyDenseEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyDenseEmbeddingUp : Type where
  | mk (R W D J S H C P N : BHist) : RealCauchyDenseEmbeddingUp
  deriving DecidableEq

def realCauchyDenseEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyDenseEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyDenseEmbeddingEncodeBHist h

def realCauchyDenseEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyDenseEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyDenseEmbeddingDecodeBHist tail)

private theorem realCauchyDenseEmbedding_decode_encode_bhist :
    ∀ h : BHist,
      realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyDenseEmbeddingFields : RealCauchyDenseEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyDenseEmbeddingUp.mk R W D J S H C P N => [R, W, D, J, S, H, C, P, N]

def realCauchyDenseEmbeddingToEventFlow : RealCauchyDenseEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realCauchyDenseEmbeddingEncodeBHist (realCauchyDenseEmbeddingFields x)

private def realCauchyDenseEmbeddingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyDenseEmbeddingEventAt index rest

def realCauchyDenseEmbeddingFromEventFlow :
    EventFlow → Option RealCauchyDenseEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (RealCauchyDenseEmbeddingUp.mk
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 0 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 1 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 2 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 3 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 4 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 5 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 6 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 7 flow))
        (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAt 8 flow)))

private theorem realCauchyDenseEmbedding_round_trip :
    ∀ x : RealCauchyDenseEmbeddingUp,
      realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D J S H C P N =>
      change
        some
            (RealCauchyDenseEmbeddingUp.mk
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist R))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist W))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist D))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist J))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist S))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist H))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist C))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist P))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist N))) =
          some (RealCauchyDenseEmbeddingUp.mk R W D J S H C P N)
      rw [realCauchyDenseEmbedding_decode_encode_bhist R,
        realCauchyDenseEmbedding_decode_encode_bhist W,
        realCauchyDenseEmbedding_decode_encode_bhist D,
        realCauchyDenseEmbedding_decode_encode_bhist J,
        realCauchyDenseEmbedding_decode_encode_bhist S,
        realCauchyDenseEmbedding_decode_encode_bhist H,
        realCauchyDenseEmbedding_decode_encode_bhist C,
        realCauchyDenseEmbedding_decode_encode_bhist P,
        realCauchyDenseEmbedding_decode_encode_bhist N]

private theorem realCauchyDenseEmbeddingToEventFlow_injective
    {x y : RealCauchyDenseEmbeddingUp} :
    realCauchyDenseEmbeddingToEventFlow x = realCauchyDenseEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
        realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow y) :=
    congrArg realCauchyDenseEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyDenseEmbedding_round_trip x).symm
      (Eq.trans hread (realCauchyDenseEmbedding_round_trip y)))

instance realCauchyDenseEmbeddingBHistCarrier :
    BHistCarrier RealCauchyDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyDenseEmbeddingToEventFlow
  fromEventFlow := realCauchyDenseEmbeddingFromEventFlow

instance realCauchyDenseEmbeddingChapterTasteGate :
    ChapterTasteGate RealCauchyDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
        some x
    exact realCauchyDenseEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyDenseEmbeddingToEventFlow_injective heq)

theorem RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment :
    (forall h : BHist,
        realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier RealCauchyDenseEmbeddingUp) ∧
        Nonempty (ChapterTasteGate RealCauchyDenseEmbeddingUp) ∧
          realCauchyDenseEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realCauchyDenseEmbedding_decode_encode_bhist,
      ⟨realCauchyDenseEmbeddingBHistCarrier⟩,
      ⟨realCauchyDenseEmbeddingChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealCauchyDenseEmbeddingUp
