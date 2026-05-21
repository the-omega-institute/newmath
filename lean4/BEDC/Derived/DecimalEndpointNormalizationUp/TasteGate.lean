import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalEndpointNormalizationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalEndpointNormalizationUp : Type where
  | mk (D E L A W Q R S H C P N : BHist) : DecimalEndpointNormalizationUp
  deriving DecidableEq

def decimalEndpointNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalEndpointNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalEndpointNormalizationEncodeBHist h

def decimalEndpointNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalEndpointNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalEndpointNormalizationDecodeBHist tail)

private theorem decimalEndpointNormalization_decode_encode :
    ∀ h : BHist,
      decimalEndpointNormalizationDecodeBHist
          (decimalEndpointNormalizationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def decimalEndpointNormalizationFields :
    DecimalEndpointNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalEndpointNormalizationUp.mk D E L A W Q R S H C P N =>
      [D, E, L, A, W, Q, R, S, H, C, P, N]

def decimalEndpointNormalizationToEventFlow :
    DecimalEndpointNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map decimalEndpointNormalizationEncodeBHist
        (decimalEndpointNormalizationFields x)

private def decimalEndpointNormalizationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => decimalEndpointNormalizationRawAt index rest

def decimalEndpointNormalizationFromEventFlow
    (flow : EventFlow) : Option DecimalEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DecimalEndpointNormalizationUp.mk
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 0 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 1 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 2 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 3 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 4 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 5 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 6 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 7 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 8 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 9 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 10 flow))
      (decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationRawAt 11 flow)))

private theorem decimalEndpointNormalization_round_trip :
    ∀ x : DecimalEndpointNormalizationUp,
      decimalEndpointNormalizationFromEventFlow
          (decimalEndpointNormalizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D E L A W Q R S H C P N =>
      change
        some
          (DecimalEndpointNormalizationUp.mk
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist D))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist E))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist L))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist A))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist W))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist Q))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist R))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist S))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist H))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist C))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist P))
            (decimalEndpointNormalizationDecodeBHist
              (decimalEndpointNormalizationEncodeBHist N))) =
          some (DecimalEndpointNormalizationUp.mk D E L A W Q R S H C P N)
      rw [decimalEndpointNormalization_decode_encode D,
        decimalEndpointNormalization_decode_encode E,
        decimalEndpointNormalization_decode_encode L,
        decimalEndpointNormalization_decode_encode A,
        decimalEndpointNormalization_decode_encode W,
        decimalEndpointNormalization_decode_encode Q,
        decimalEndpointNormalization_decode_encode R,
        decimalEndpointNormalization_decode_encode S,
        decimalEndpointNormalization_decode_encode H,
        decimalEndpointNormalization_decode_encode C,
        decimalEndpointNormalization_decode_encode P,
        decimalEndpointNormalization_decode_encode N]

private theorem decimalEndpointNormalizationToEventFlow_injective
    {x y : DecimalEndpointNormalizationUp} :
    decimalEndpointNormalizationToEventFlow x =
        decimalEndpointNormalizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decimalEndpointNormalizationFromEventFlow
          (decimalEndpointNormalizationToEventFlow x) =
        decimalEndpointNormalizationFromEventFlow
          (decimalEndpointNormalizationToEventFlow y) :=
    congrArg decimalEndpointNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (decimalEndpointNormalization_round_trip x).symm
      (Eq.trans hread (decimalEndpointNormalization_round_trip y)))

instance decimalEndpointNormalizationBHistCarrier :
    BHistCarrier DecimalEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalEndpointNormalizationToEventFlow
  fromEventFlow := decimalEndpointNormalizationFromEventFlow

instance decimalEndpointNormalizationChapterTasteGate :
    ChapterTasteGate DecimalEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      decimalEndpointNormalizationFromEventFlow
          (decimalEndpointNormalizationToEventFlow x) =
        some x
    exact decimalEndpointNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (decimalEndpointNormalizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DecimalEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  decimalEndpointNormalizationChapterTasteGate

theorem DecimalEndpointNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      decimalEndpointNormalizationDecodeBHist
          (decimalEndpointNormalizationEncodeBHist h) =
        h) ∧
      (∀ x : DecimalEndpointNormalizationUp,
        decimalEndpointNormalizationFromEventFlow
            (decimalEndpointNormalizationToEventFlow x) =
          some x) ∧
        (∀ x y : DecimalEndpointNormalizationUp,
          decimalEndpointNormalizationToEventFlow x =
              decimalEndpointNormalizationToEventFlow y →
            x = y) ∧
          decimalEndpointNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨decimalEndpointNormalization_decode_encode,
      decimalEndpointNormalization_round_trip,
      by
        intro x y heq
        exact decimalEndpointNormalizationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DecimalEndpointNormalizationUp.TasteGate
