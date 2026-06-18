import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlternatingHarmonicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlternatingHarmonicUp : Type where
  | mk (S L D R E H C P N : BHist) : AlternatingHarmonicUp
  deriving DecidableEq

def alternatingHarmonicEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: alternatingHarmonicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: alternatingHarmonicEncodeBHist h

def alternatingHarmonicDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (alternatingHarmonicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (alternatingHarmonicDecodeBHist tail)

private theorem alternatingHarmonicDecode_encode_bhist :
    ∀ h : BHist,
      alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def alternatingHarmonicToEventFlow : AlternatingHarmonicUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AlternatingHarmonicUp.mk S L D R E H C P N =>
      [alternatingHarmonicEncodeBHist S,
        alternatingHarmonicEncodeBHist L,
        alternatingHarmonicEncodeBHist D,
        alternatingHarmonicEncodeBHist R,
        alternatingHarmonicEncodeBHist E,
        alternatingHarmonicEncodeBHist H,
        alternatingHarmonicEncodeBHist C,
        alternatingHarmonicEncodeBHist P,
        alternatingHarmonicEncodeBHist N]

private def alternatingHarmonicRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => alternatingHarmonicRawAt n rest

private def alternatingHarmonicLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => alternatingHarmonicLengthEq n rest

def alternatingHarmonicFromEventFlow : EventFlow → Option AlternatingHarmonicUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match alternatingHarmonicLengthEq 9 flow with
      | true =>
          some
            (AlternatingHarmonicUp.mk
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 0 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 1 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 2 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 3 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 4 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 5 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 6 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 7 flow))
              (alternatingHarmonicDecodeBHist (alternatingHarmonicRawAt 8 flow)))
      | false => none

private theorem alternatingHarmonic_round_trip :
    ∀ x : AlternatingHarmonicUp,
      alternatingHarmonicFromEventFlow (alternatingHarmonicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L D R E H C P N =>
      change
        some
          (AlternatingHarmonicUp.mk
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist S))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist L))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist D))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist R))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist E))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist H))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist C))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist P))
            (alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist N))) =
          some (AlternatingHarmonicUp.mk S L D R E H C P N)
      rw [alternatingHarmonicDecode_encode_bhist S,
        alternatingHarmonicDecode_encode_bhist L,
        alternatingHarmonicDecode_encode_bhist D,
        alternatingHarmonicDecode_encode_bhist R,
        alternatingHarmonicDecode_encode_bhist E,
        alternatingHarmonicDecode_encode_bhist H,
        alternatingHarmonicDecode_encode_bhist C,
        alternatingHarmonicDecode_encode_bhist P,
        alternatingHarmonicDecode_encode_bhist N]

private theorem alternatingHarmonicToEventFlow_injective {x y : AlternatingHarmonicUp} :
    alternatingHarmonicToEventFlow x = alternatingHarmonicToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      alternatingHarmonicFromEventFlow (alternatingHarmonicToEventFlow x) =
        alternatingHarmonicFromEventFlow (alternatingHarmonicToEventFlow y) :=
    congrArg alternatingHarmonicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (alternatingHarmonic_round_trip x).symm
      (Eq.trans hread (alternatingHarmonic_round_trip y)))

instance alternatingHarmonicBHistCarrier : BHistCarrier AlternatingHarmonicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := alternatingHarmonicToEventFlow
  fromEventFlow := alternatingHarmonicFromEventFlow

instance alternatingHarmonicChapterTasteGate : ChapterTasteGate AlternatingHarmonicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change alternatingHarmonicFromEventFlow (alternatingHarmonicToEventFlow x) = some x
    exact alternatingHarmonic_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (alternatingHarmonicToEventFlow_injective heq)

theorem AlternatingHarmonicTasteGate_single_carrier_alignment :
    (∀ h : BHist, alternatingHarmonicDecodeBHist (alternatingHarmonicEncodeBHist h) = h) ∧
      (∀ x : AlternatingHarmonicUp,
        alternatingHarmonicFromEventFlow (alternatingHarmonicToEventFlow x) = some x) ∧
        (∀ x y : AlternatingHarmonicUp,
          alternatingHarmonicToEventFlow x = alternatingHarmonicToEventFlow y → x = y) ∧
          alternatingHarmonicEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨alternatingHarmonicDecode_encode_bhist,
      alternatingHarmonic_round_trip,
      by
        intro x y heq
        exact alternatingHarmonicToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AlternatingHarmonicUp
