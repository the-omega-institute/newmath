import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinaryEndpointNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BinaryEndpointNormalizationUp : Type where
  | mk (L R K D A W Q S H C P N : BHist) : BinaryEndpointNormalizationUp
  deriving DecidableEq

def binaryEndpointNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: binaryEndpointNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: binaryEndpointNormalizationEncodeBHist h

def binaryEndpointNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (binaryEndpointNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (binaryEndpointNormalizationDecodeBHist tail)

private theorem binaryEndpointNormalization_decode_encode :
    ∀ h : BHist,
      binaryEndpointNormalizationDecodeBHist
          (binaryEndpointNormalizationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def binaryEndpointNormalizationFields :
    BinaryEndpointNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N =>
      [L, R, K, D, A, W, Q, S, H, C, P, N]

def binaryEndpointNormalizationToEventFlow :
    BinaryEndpointNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map binaryEndpointNormalizationEncodeBHist
        (binaryEndpointNormalizationFields x)

private def binaryEndpointNormalizationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => binaryEndpointNormalizationRawAt index rest

def binaryEndpointNormalizationFromEventFlow
    (flow : EventFlow) : Option BinaryEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BinaryEndpointNormalizationUp.mk
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 0 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 1 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 2 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 3 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 4 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 5 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 6 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 7 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 8 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 9 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 10 flow))
      (binaryEndpointNormalizationDecodeBHist (binaryEndpointNormalizationRawAt 11 flow)))

private theorem binaryEndpointNormalization_round_trip :
    ∀ x : BinaryEndpointNormalizationUp,
      binaryEndpointNormalizationFromEventFlow
          (binaryEndpointNormalizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R K D A W Q S H C P N =>
      change
        some
          (BinaryEndpointNormalizationUp.mk
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist L))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist R))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist K))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist D))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist A))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist W))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist Q))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist S))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist H))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist C))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist P))
            (binaryEndpointNormalizationDecodeBHist
              (binaryEndpointNormalizationEncodeBHist N))) =
          some (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N)
      rw [binaryEndpointNormalization_decode_encode L,
        binaryEndpointNormalization_decode_encode R,
        binaryEndpointNormalization_decode_encode K,
        binaryEndpointNormalization_decode_encode D,
        binaryEndpointNormalization_decode_encode A,
        binaryEndpointNormalization_decode_encode W,
        binaryEndpointNormalization_decode_encode Q,
        binaryEndpointNormalization_decode_encode S,
        binaryEndpointNormalization_decode_encode H,
        binaryEndpointNormalization_decode_encode C,
        binaryEndpointNormalization_decode_encode P,
        binaryEndpointNormalization_decode_encode N]

private theorem binaryEndpointNormalizationToEventFlow_injective
    {x y : BinaryEndpointNormalizationUp} :
    binaryEndpointNormalizationToEventFlow x =
        binaryEndpointNormalizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      binaryEndpointNormalizationFromEventFlow
          (binaryEndpointNormalizationToEventFlow x) =
        binaryEndpointNormalizationFromEventFlow
          (binaryEndpointNormalizationToEventFlow y) :=
    congrArg binaryEndpointNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (binaryEndpointNormalization_round_trip x).symm
      (Eq.trans hread (binaryEndpointNormalization_round_trip y)))

instance binaryEndpointNormalizationBHistCarrier :
    BHistCarrier BinaryEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := binaryEndpointNormalizationToEventFlow
  fromEventFlow := binaryEndpointNormalizationFromEventFlow

instance binaryEndpointNormalizationChapterTasteGate :
    ChapterTasteGate BinaryEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      binaryEndpointNormalizationFromEventFlow
          (binaryEndpointNormalizationToEventFlow x) =
        some x
    exact binaryEndpointNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (binaryEndpointNormalizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BinaryEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  binaryEndpointNormalizationChapterTasteGate

theorem BinaryEndpointNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      binaryEndpointNormalizationDecodeBHist
          (binaryEndpointNormalizationEncodeBHist h) =
        h) ∧
      (∀ x : BinaryEndpointNormalizationUp,
        binaryEndpointNormalizationFromEventFlow
            (binaryEndpointNormalizationToEventFlow x) =
          some x) ∧
        (∀ x y : BinaryEndpointNormalizationUp,
          binaryEndpointNormalizationToEventFlow x =
              binaryEndpointNormalizationToEventFlow y →
            x = y) ∧
          binaryEndpointNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨binaryEndpointNormalization_decode_encode,
      binaryEndpointNormalization_round_trip,
      by
        intro x y heq
        exact binaryEndpointNormalizationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BinaryEndpointNormalizationUp
