import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalCauchyFilterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalCauchyFilterUp : Type where
  | mk (F S R T D E H C P N : BHist) : MinimalCauchyFilterUp
  deriving DecidableEq

def minimalCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalCauchyFilterEncodeBHist h

def minimalCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalCauchyFilterDecodeBHist tail)

private theorem minimalCauchyFilter_decode_encode_bhist :
    ∀ h : BHist, minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def minimalCauchyFilterToEventFlow : MinimalCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalCauchyFilterUp.mk F S R T D E H C P N =>
      [minimalCauchyFilterEncodeBHist F,
        minimalCauchyFilterEncodeBHist S,
        minimalCauchyFilterEncodeBHist R,
        minimalCauchyFilterEncodeBHist T,
        minimalCauchyFilterEncodeBHist D,
        minimalCauchyFilterEncodeBHist E,
        minimalCauchyFilterEncodeBHist H,
        minimalCauchyFilterEncodeBHist C,
        minimalCauchyFilterEncodeBHist P,
        minimalCauchyFilterEncodeBHist N]

private def minimalCauchyFilterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => minimalCauchyFilterEventAt index rest

def minimalCauchyFilterFromEventFlow : EventFlow → Option MinimalCauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MinimalCauchyFilterUp.mk
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 0 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 1 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 2 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 3 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 4 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 5 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 6 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 7 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 8 ef))
          (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEventAt 9 ef)))

private theorem minimalCauchyFilter_round_trip :
    ∀ x : MinimalCauchyFilterUp,
      minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S R T D E H C P N =>
      change
        some
          (MinimalCauchyFilterUp.mk
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist F))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist S))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist R))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist T))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist D))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist E))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist H))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist C))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist P))
            (minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist N))) =
          some (MinimalCauchyFilterUp.mk F S R T D E H C P N)
      rw [minimalCauchyFilter_decode_encode_bhist F,
        minimalCauchyFilter_decode_encode_bhist S,
        minimalCauchyFilter_decode_encode_bhist R,
        minimalCauchyFilter_decode_encode_bhist T,
        minimalCauchyFilter_decode_encode_bhist D,
        minimalCauchyFilter_decode_encode_bhist E,
        minimalCauchyFilter_decode_encode_bhist H,
        minimalCauchyFilter_decode_encode_bhist C,
        minimalCauchyFilter_decode_encode_bhist P,
        minimalCauchyFilter_decode_encode_bhist N]

private theorem minimalCauchyFilterToEventFlow_injective
    {x y : MinimalCauchyFilterUp} :
    minimalCauchyFilterToEventFlow x = minimalCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) =
        minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow y) :=
    congrArg minimalCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (minimalCauchyFilter_round_trip x).symm
      (Eq.trans hread (minimalCauchyFilter_round_trip y)))

instance minimalCauchyFilterBHistCarrier : BHistCarrier MinimalCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalCauchyFilterToEventFlow
  fromEventFlow := minimalCauchyFilterFromEventFlow

instance minimalCauchyFilterChapterTasteGate :
    ChapterTasteGate MinimalCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) = some x
    exact minimalCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (minimalCauchyFilterToEventFlow_injective heq)

theorem MinimalCauchyFilterUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist h) = h) ∧
      (∀ x : MinimalCauchyFilterUp,
        minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) = some x) ∧
      (∀ x y : MinimalCauchyFilterUp,
        minimalCauchyFilterToEventFlow x = minimalCauchyFilterToEventFlow y → x = y) ∧
      minimalCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨minimalCauchyFilter_decode_encode_bhist, minimalCauchyFilter_round_trip,
    fun _ _ heq => minimalCauchyFilterToEventFlow_injective heq, rfl⟩

end BEDC.Derived.MinimalCauchyFilterUp.TasteGate
