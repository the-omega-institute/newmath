import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableMetricNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableMetricNameUp : Type where
  | mk (S M W D R E H C P N : BHist) : CountableMetricNameUp
  deriving DecidableEq

def countableMetricNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableMetricNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countableMetricNameEncodeBHist h

def countableMetricNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableMetricNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countableMetricNameDecodeBHist tail)

private theorem CountableMetricNameTasteGate_decode_encode :
    ∀ h : BHist, countableMetricNameDecodeBHist (countableMetricNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def countableMetricNameFields : CountableMetricNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountableMetricNameUp.mk S M W D R E H C P N => [S, M, W, D, R, E, H, C, P, N]

def countableMetricNameToEventFlow : CountableMetricNameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (countableMetricNameFields x).map countableMetricNameEncodeBHist

def countableMetricNameFromEventFlow : EventFlow → Option CountableMetricNameUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, M, W, D, R, E, H, C, P, N] =>
      some
        (CountableMetricNameUp.mk
          (countableMetricNameDecodeBHist S)
          (countableMetricNameDecodeBHist M)
          (countableMetricNameDecodeBHist W)
          (countableMetricNameDecodeBHist D)
          (countableMetricNameDecodeBHist R)
          (countableMetricNameDecodeBHist E)
          (countableMetricNameDecodeBHist H)
          (countableMetricNameDecodeBHist C)
          (countableMetricNameDecodeBHist P)
          (countableMetricNameDecodeBHist N))
  | _ => none

private theorem CountableMetricNameTasteGate_round_trip :
    ∀ x : CountableMetricNameUp,
      countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W D R E H C P N =>
      change
        some
          (CountableMetricNameUp.mk
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist S))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist M))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist W))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist D))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist R))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist E))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist H))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist C))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist P))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist N))) =
          some (CountableMetricNameUp.mk S M W D R E H C P N)
      rw [CountableMetricNameTasteGate_decode_encode S,
        CountableMetricNameTasteGate_decode_encode M,
        CountableMetricNameTasteGate_decode_encode W,
        CountableMetricNameTasteGate_decode_encode D,
        CountableMetricNameTasteGate_decode_encode R,
        CountableMetricNameTasteGate_decode_encode E,
        CountableMetricNameTasteGate_decode_encode H,
        CountableMetricNameTasteGate_decode_encode C,
        CountableMetricNameTasteGate_decode_encode P,
        CountableMetricNameTasteGate_decode_encode N]

private theorem CountableMetricNameTasteGate_toEventFlow_injective {x y : CountableMetricNameUp} :
    countableMetricNameToEventFlow x = countableMetricNameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) =
        countableMetricNameFromEventFlow (countableMetricNameToEventFlow y) :=
    congrArg countableMetricNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CountableMetricNameTasteGate_round_trip x).symm
      (Eq.trans hread (CountableMetricNameTasteGate_round_trip y)))

instance countableMetricNameBHistCarrier : BHistCarrier CountableMetricNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableMetricNameToEventFlow
  fromEventFlow := countableMetricNameFromEventFlow

instance countableMetricNameChapterTasteGate : ChapterTasteGate CountableMetricNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) = some x
    exact CountableMetricNameTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CountableMetricNameTasteGate_toEventFlow_injective heq)

theorem CountableMetricNameTasteGate_single_carrier_alignment :
    (∀ h : BHist, countableMetricNameDecodeBHist (countableMetricNameEncodeBHist h) = h) ∧
      (∀ x : CountableMetricNameUp,
        countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) = some x) ∧
      (∀ x y : CountableMetricNameUp,
        countableMetricNameToEventFlow x = countableMetricNameToEventFlow y → x = y) ∧
      countableMetricNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CountableMetricNameTasteGate_decode_encode
  constructor
  · exact CountableMetricNameTasteGate_round_trip
  constructor
  · intro x y heq
    exact CountableMetricNameTasteGate_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CountableMetricNameUp
