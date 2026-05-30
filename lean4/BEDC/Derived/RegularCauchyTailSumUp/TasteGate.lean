import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailSumUp : Type where
  | mk (D S R A W B E H C P N : BHist) : RegularCauchyTailSumUp
  deriving DecidableEq

def regularCauchyTailSumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailSumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailSumEncodeBHist h

def regularCauchyTailSumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailSumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailSumDecodeBHist tail)

private theorem RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailSumToEventFlow : RegularCauchyTailSumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailSumUp.mk D S R A W B E H C P N =>
      [[BMark.b0],
        regularCauchyTailSumEncodeBHist D,
        [BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyTailSumEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailSumEncodeBHist N]

private def regularCauchyTailSumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailSumEventAtDefault index rest

def regularCauchyTailSumFromEventFlow (ef : EventFlow) : Option RegularCauchyTailSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailSumUp.mk
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 1 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 3 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 5 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 7 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 9 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 11 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 13 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 15 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 17 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 19 ef))
      (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEventAtDefault 21 ef)))

private theorem RegularCauchyTailSumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyTailSumUp,
      regularCauchyTailSumFromEventFlow (regularCauchyTailSumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R A W B E H C P N =>
      change
        some
          (RegularCauchyTailSumUp.mk
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist D))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist S))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist R))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist A))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist W))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist B))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist E))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist H))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist C))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist P))
            (regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist N))) =
          some (RegularCauchyTailSumUp.mk D S R A W B E H C P N)
      rw [RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyTailSumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTailSumUp} :
    regularCauchyTailSumToEventFlow x = regularCauchyTailSumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailSumFromEventFlow (regularCauchyTailSumToEventFlow x) =
        regularCauchyTailSumFromEventFlow (regularCauchyTailSumToEventFlow y) :=
    congrArg regularCauchyTailSumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailSumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyTailSumTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyTailSumBHistCarrier : BHistCarrier RegularCauchyTailSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailSumToEventFlow
  fromEventFlow := regularCauchyTailSumFromEventFlow

instance regularCauchyTailSumChapterTasteGate : ChapterTasteGate RegularCauchyTailSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTailSumFromEventFlow (regularCauchyTailSumToEventFlow x) = some x
    exact RegularCauchyTailSumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyTailSumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyTailSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailSumChapterTasteGate

theorem RegularCauchyTailSumTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyTailSumDecodeBHist (regularCauchyTailSumEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailSumUp,
        regularCauchyTailSumFromEventFlow (regularCauchyTailSumToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailSumUp,
          regularCauchyTailSumToEventFlow x = regularCauchyTailSumToEventFlow y → x = y) ∧
          regularCauchyTailSumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyTailSumTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyTailSumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularCauchyTailSumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyTailSumUp
