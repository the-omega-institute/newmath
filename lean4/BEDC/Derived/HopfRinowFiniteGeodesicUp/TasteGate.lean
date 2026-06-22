import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HopfRinowFiniteGeodesicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HopfRinowFiniteGeodesicUp : Type where
  | mk (C M R K S Q A H T P N : BHist) : HopfRinowFiniteGeodesicUp
  deriving DecidableEq

def hopfRinowFiniteGeodesicEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hopfRinowFiniteGeodesicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hopfRinowFiniteGeodesicEncodeBHist h

def hopfRinowFiniteGeodesicDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hopfRinowFiniteGeodesicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hopfRinowFiniteGeodesicDecodeBHist tail)

private theorem hopfRinowFiniteGeodesic_decode_encode_bhist :
    ∀ h : BHist,
      hopfRinowFiniteGeodesicDecodeBHist
        (hopfRinowFiniteGeodesicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hopfRinowFiniteGeodesicFields : HopfRinowFiniteGeodesicUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HopfRinowFiniteGeodesicUp.mk C M R K S Q A H T P N =>
      [C, M, R, K, S, Q, A, H, T, P, N]

def hopfRinowFiniteGeodesicToEventFlow : HopfRinowFiniteGeodesicUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hopfRinowFiniteGeodesicFields x).map hopfRinowFiniteGeodesicEncodeBHist

private def hopfRinowFiniteGeodesicEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hopfRinowFiniteGeodesicEventAt index rest

def hopfRinowFiniteGeodesicFromEventFlow
    (ef : EventFlow) : Option HopfRinowFiniteGeodesicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HopfRinowFiniteGeodesicUp.mk
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 0 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 1 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 2 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 3 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 4 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 5 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 6 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 7 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 8 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 9 ef))
      (hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEventAt 10 ef)))

private theorem hopfRinowFiniteGeodesic_round_trip
    (x : HopfRinowFiniteGeodesicUp) :
    hopfRinowFiniteGeodesicFromEventFlow
        (hopfRinowFiniteGeodesicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C M R K S Q A H T P N =>
      change
        some
          (HopfRinowFiniteGeodesicUp.mk
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist C))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist M))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist R))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist K))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist S))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist Q))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist A))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist H))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist T))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist P))
            (hopfRinowFiniteGeodesicDecodeBHist
              (hopfRinowFiniteGeodesicEncodeBHist N))) =
          some (HopfRinowFiniteGeodesicUp.mk C M R K S Q A H T P N)
      rw [hopfRinowFiniteGeodesic_decode_encode_bhist C,
        hopfRinowFiniteGeodesic_decode_encode_bhist M,
        hopfRinowFiniteGeodesic_decode_encode_bhist R,
        hopfRinowFiniteGeodesic_decode_encode_bhist K,
        hopfRinowFiniteGeodesic_decode_encode_bhist S,
        hopfRinowFiniteGeodesic_decode_encode_bhist Q,
        hopfRinowFiniteGeodesic_decode_encode_bhist A,
        hopfRinowFiniteGeodesic_decode_encode_bhist H,
        hopfRinowFiniteGeodesic_decode_encode_bhist T,
        hopfRinowFiniteGeodesic_decode_encode_bhist P,
        hopfRinowFiniteGeodesic_decode_encode_bhist N]

private theorem hopfRinowFiniteGeodesicToEventFlow_injective
    {x y : HopfRinowFiniteGeodesicUp} :
    hopfRinowFiniteGeodesicToEventFlow x =
      hopfRinowFiniteGeodesicToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hopfRinowFiniteGeodesicFromEventFlow (hopfRinowFiniteGeodesicToEventFlow x) =
        hopfRinowFiniteGeodesicFromEventFlow (hopfRinowFiniteGeodesicToEventFlow y) :=
    congrArg hopfRinowFiniteGeodesicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hopfRinowFiniteGeodesic_round_trip x).symm
      (Eq.trans hread (hopfRinowFiniteGeodesic_round_trip y)))

instance hopfRinowFiniteGeodesicBHistCarrier :
    BHistCarrier HopfRinowFiniteGeodesicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hopfRinowFiniteGeodesicToEventFlow
  fromEventFlow := hopfRinowFiniteGeodesicFromEventFlow

instance hopfRinowFiniteGeodesicChapterTasteGate :
    ChapterTasteGate HopfRinowFiniteGeodesicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hopfRinowFiniteGeodesicFromEventFlow (hopfRinowFiniteGeodesicToEventFlow x) =
        some x
    exact hopfRinowFiniteGeodesic_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hopfRinowFiniteGeodesicToEventFlow_injective heq)

theorem HopfRinowFiniteGeodesicTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hopfRinowFiniteGeodesicDecodeBHist (hopfRinowFiniteGeodesicEncodeBHist h) =
        h) ∧
      (∀ x : HopfRinowFiniteGeodesicUp,
        hopfRinowFiniteGeodesicFromEventFlow
          (hopfRinowFiniteGeodesicToEventFlow x) = some x) ∧
        (∀ x y : HopfRinowFiniteGeodesicUp,
          hopfRinowFiniteGeodesicToEventFlow x =
            hopfRinowFiniteGeodesicToEventFlow y → x = y) ∧
          hopfRinowFiniteGeodesicEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨hopfRinowFiniteGeodesic_decode_encode_bhist,
      hopfRinowFiniteGeodesic_round_trip,
      (fun _ _ heq => hopfRinowFiniteGeodesicToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HopfRinowFiniteGeodesicUp
