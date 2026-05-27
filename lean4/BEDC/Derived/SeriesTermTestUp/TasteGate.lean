import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeriesTermTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeriesTermTestUp : Type where
  | mk (T S A D R Z H C P N : BHist) : SeriesTermTestUp
  deriving DecidableEq

def seriesTermTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: seriesTermTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: seriesTermTestEncodeBHist h

def seriesTermTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (seriesTermTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (seriesTermTestDecodeBHist tail)

private theorem seriesTermTest_decode_encode_bhist :
    ∀ h : BHist, seriesTermTestDecodeBHist (seriesTermTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def seriesTermTestFields : SeriesTermTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeriesTermTestUp.mk T S A D R Z H C P N => [T, S, A, D, R, Z, H, C, P, N]

def seriesTermTestToEventFlow : SeriesTermTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (seriesTermTestFields x).map seriesTermTestEncodeBHist

private def seriesTermTestRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => seriesTermTestRawAt n rest

private def seriesTermTestLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => seriesTermTestLengthEq n rest

def seriesTermTestFromEventFlow : EventFlow → Option SeriesTermTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match seriesTermTestLengthEq 10 flow with
      | true =>
          some
            (SeriesTermTestUp.mk
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 0 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 1 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 2 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 3 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 4 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 5 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 6 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 7 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 8 flow))
              (seriesTermTestDecodeBHist (seriesTermTestRawAt 9 flow)))
      | false => none

private theorem seriesTermTest_round_trip :
    ∀ x : SeriesTermTestUp,
      seriesTermTestFromEventFlow (seriesTermTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S A D R Z H C P N =>
      change
        some
          (SeriesTermTestUp.mk
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist T))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist S))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist A))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist D))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist R))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist Z))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist H))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist C))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist P))
            (seriesTermTestDecodeBHist (seriesTermTestEncodeBHist N))) =
          some (SeriesTermTestUp.mk T S A D R Z H C P N)
      rw [seriesTermTest_decode_encode_bhist T,
        seriesTermTest_decode_encode_bhist S,
        seriesTermTest_decode_encode_bhist A,
        seriesTermTest_decode_encode_bhist D,
        seriesTermTest_decode_encode_bhist R,
        seriesTermTest_decode_encode_bhist Z,
        seriesTermTest_decode_encode_bhist H,
        seriesTermTest_decode_encode_bhist C,
        seriesTermTest_decode_encode_bhist P,
        seriesTermTest_decode_encode_bhist N]

private theorem seriesTermTestToEventFlow_injective {x y : SeriesTermTestUp} :
    seriesTermTestToEventFlow x = seriesTermTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      seriesTermTestFromEventFlow (seriesTermTestToEventFlow x) =
        seriesTermTestFromEventFlow (seriesTermTestToEventFlow y) :=
    congrArg seriesTermTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (seriesTermTest_round_trip x).symm
      (Eq.trans hread (seriesTermTest_round_trip y)))

instance seriesTermTestBHistCarrier : BHistCarrier SeriesTermTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := seriesTermTestToEventFlow
  fromEventFlow := seriesTermTestFromEventFlow

instance seriesTermTestChapterTasteGate : ChapterTasteGate SeriesTermTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change seriesTermTestFromEventFlow (seriesTermTestToEventFlow x) = some x
    exact seriesTermTest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (seriesTermTestToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SeriesTermTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  seriesTermTestChapterTasteGate

theorem SeriesTermTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, seriesTermTestDecodeBHist (seriesTermTestEncodeBHist h) = h) ∧
      (∀ x : SeriesTermTestUp,
        seriesTermTestFromEventFlow (seriesTermTestToEventFlow x) = some x) ∧
        (∀ x y : SeriesTermTestUp,
          seriesTermTestToEventFlow x = seriesTermTestToEventFlow y → x = y) ∧
          seriesTermTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨seriesTermTest_decode_encode_bhist,
      seriesTermTest_round_trip,
      fun _ _ heq => seriesTermTestToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.SeriesTermTestUp
