import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalEmbeddingUp : Type where
  | mk
      (dyadicEndpoint streamWindow regularReadback realConsumer transport replay provenance
        localName : BHist) :
      RegularCauchyDiagonalEmbeddingUp
  deriving DecidableEq

def regularCauchyDiagonalEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalEmbeddingEncodeBHist h

def regularCauchyDiagonalEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalEmbeddingDecodeBHist tail)

private theorem regularCauchyDiagonalEmbeddingDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyDiagonalEmbeddingToEventFlow :
    RegularCauchyDiagonalEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalEmbeddingUp.mk dyadicEndpoint streamWindow regularReadback
      realConsumer transport replay provenance localName =>
      [[BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist dyadicEndpoint,
        [BMark.b1, BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist realConsumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyDiagonalEmbeddingEncodeBHist localName]

private def regularCauchyDiagonalEmbeddingRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDiagonalEmbeddingRawAt index rest

def regularCauchyDiagonalEmbeddingFromEventFlow (flow : EventFlow) :
    Option RegularCauchyDiagonalEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDiagonalEmbeddingUp.mk
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 1 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 3 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 5 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 7 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 9 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 11 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 13 flow))
      (regularCauchyDiagonalEmbeddingDecodeBHist
        (regularCauchyDiagonalEmbeddingRawAt 15 flow)))

private theorem regularCauchyDiagonalEmbedding_round_trip :
    ∀ x : RegularCauchyDiagonalEmbeddingUp,
      regularCauchyDiagonalEmbeddingFromEventFlow
        (regularCauchyDiagonalEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadicEndpoint streamWindow regularReadback realConsumer transport replay provenance
      localName =>
      change
        some
          (RegularCauchyDiagonalEmbeddingUp.mk
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist dyadicEndpoint))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist streamWindow))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist regularReadback))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist realConsumer))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist transport))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist replay))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist provenance))
            (regularCauchyDiagonalEmbeddingDecodeBHist
              (regularCauchyDiagonalEmbeddingEncodeBHist localName))) =
          some
            (RegularCauchyDiagonalEmbeddingUp.mk dyadicEndpoint streamWindow regularReadback
              realConsumer transport replay provenance localName)
      rw [regularCauchyDiagonalEmbeddingDecode_encode_bhist dyadicEndpoint,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist streamWindow,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist regularReadback,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist realConsumer,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist transport,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist replay,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist provenance,
        regularCauchyDiagonalEmbeddingDecode_encode_bhist localName]

private theorem regularCauchyDiagonalEmbeddingToEventFlow_injective
    {x y : RegularCauchyDiagonalEmbeddingUp} :
    regularCauchyDiagonalEmbeddingToEventFlow x =
      regularCauchyDiagonalEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalEmbeddingFromEventFlow
          (regularCauchyDiagonalEmbeddingToEventFlow x) =
        regularCauchyDiagonalEmbeddingFromEventFlow
          (regularCauchyDiagonalEmbeddingToEventFlow y) :=
    congrArg regularCauchyDiagonalEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDiagonalEmbedding_round_trip x).symm
      (Eq.trans hread (regularCauchyDiagonalEmbedding_round_trip y)))

instance regularCauchyDiagonalEmbeddingBHistCarrier :
    BHistCarrier RegularCauchyDiagonalEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalEmbeddingToEventFlow
  fromEventFlow := regularCauchyDiagonalEmbeddingFromEventFlow

instance regularCauchyDiagonalEmbeddingChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalEmbeddingFromEventFlow
        (regularCauchyDiagonalEmbeddingToEventFlow x) = some x
    exact regularCauchyDiagonalEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyDiagonalEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDiagonalEmbeddingChapterTasteGate

theorem RegularCauchyDiagonalEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyDiagonalEmbeddingUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyDiagonalEmbeddingUp) ∧
        (∀ h : BHist,
          regularCauchyDiagonalEmbeddingDecodeBHist
            (regularCauchyDiagonalEmbeddingEncodeBHist h) = h) ∧
          (∀ x : RegularCauchyDiagonalEmbeddingUp,
            regularCauchyDiagonalEmbeddingFromEventFlow
              (regularCauchyDiagonalEmbeddingToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyDiagonalEmbeddingBHistCarrier⟩
  · constructor
    · exact ⟨regularCauchyDiagonalEmbeddingChapterTasteGate⟩
    · constructor
      · exact regularCauchyDiagonalEmbeddingDecode_encode_bhist
      · exact regularCauchyDiagonalEmbedding_round_trip

end BEDC.Derived.RegularCauchyDiagonalEmbeddingUp
