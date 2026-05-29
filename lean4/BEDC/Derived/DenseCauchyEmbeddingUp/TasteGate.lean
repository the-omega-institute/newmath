import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenseCauchyEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenseCauchyEmbeddingUp : Type where
  | mk (M D Q J L H C P N : BHist) : DenseCauchyEmbeddingUp
  deriving DecidableEq

def denseCauchyEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denseCauchyEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denseCauchyEmbeddingEncodeBHist h

def denseCauchyEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denseCauchyEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denseCauchyEmbeddingDecodeBHist tail)

private theorem denseCauchyEmbedding_decode_encode_bhist :
    ∀ h : BHist, denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def denseCauchyEmbeddingFields : DenseCauchyEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenseCauchyEmbeddingUp.mk M D Q J L H C P N => [M, D, Q, J, L, H, C, P, N]

def denseCauchyEmbeddingToEventFlow : DenseCauchyEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (denseCauchyEmbeddingFields x).map denseCauchyEmbeddingEncodeBHist

private def denseCauchyEmbeddingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => denseCauchyEmbeddingEventAt index rest

def denseCauchyEmbeddingFromEventFlow (flow : EventFlow) : Option DenseCauchyEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenseCauchyEmbeddingUp.mk
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 0 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 1 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 2 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 3 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 4 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 5 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 6 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 7 flow))
      (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEventAt 8 flow)))

private theorem denseCauchyEmbedding_round_trip :
    ∀ x : DenseCauchyEmbeddingUp,
      denseCauchyEmbeddingFromEventFlow (denseCauchyEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D Q J L H C P N =>
      change
        some
          (DenseCauchyEmbeddingUp.mk
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist M))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist D))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist Q))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist J))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist L))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist H))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist C))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist P))
            (denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist N))) =
          some (DenseCauchyEmbeddingUp.mk M D Q J L H C P N)
      rw [denseCauchyEmbedding_decode_encode_bhist M,
        denseCauchyEmbedding_decode_encode_bhist D,
        denseCauchyEmbedding_decode_encode_bhist Q,
        denseCauchyEmbedding_decode_encode_bhist J,
        denseCauchyEmbedding_decode_encode_bhist L,
        denseCauchyEmbedding_decode_encode_bhist H,
        denseCauchyEmbedding_decode_encode_bhist C,
        denseCauchyEmbedding_decode_encode_bhist P,
        denseCauchyEmbedding_decode_encode_bhist N]

private theorem denseCauchyEmbeddingToEventFlow_injective {x y : DenseCauchyEmbeddingUp} :
    denseCauchyEmbeddingToEventFlow x = denseCauchyEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denseCauchyEmbeddingFromEventFlow (denseCauchyEmbeddingToEventFlow x) =
        denseCauchyEmbeddingFromEventFlow (denseCauchyEmbeddingToEventFlow y) :=
    congrArg denseCauchyEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (denseCauchyEmbedding_round_trip x).symm
      (Eq.trans hread (denseCauchyEmbedding_round_trip y)))

instance denseCauchyEmbeddingBHistCarrier : BHistCarrier DenseCauchyEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denseCauchyEmbeddingToEventFlow
  fromEventFlow := denseCauchyEmbeddingFromEventFlow

instance denseCauchyEmbeddingChapterTasteGate : ChapterTasteGate DenseCauchyEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denseCauchyEmbeddingFromEventFlow (denseCauchyEmbeddingToEventFlow x) = some x
    exact denseCauchyEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (denseCauchyEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DenseCauchyEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denseCauchyEmbeddingChapterTasteGate

theorem DenseCauchyEmbeddingTasteGate_single_carrier_alignment :
    (forall h : BHist, denseCauchyEmbeddingDecodeBHist (denseCauchyEmbeddingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DenseCauchyEmbeddingUp) ∧
        Nonempty (ChapterTasteGate DenseCauchyEmbeddingUp) ∧
          denseCauchyEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact denseCauchyEmbedding_decode_encode_bhist
  · constructor
    · exact ⟨denseCauchyEmbeddingBHistCarrier⟩
    · constructor
      · exact ⟨denseCauchyEmbeddingChapterTasteGate⟩
      · rfl

end BEDC.Derived.DenseCauchyEmbeddingUp
