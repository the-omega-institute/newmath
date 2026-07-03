import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularRealFamilyDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularRealFamilyDiagonalUp : Type where
  | mk (S R D Z E H C P N : BHist) : RegularRealFamilyDiagonalUp
  deriving DecidableEq

def regularRealFamilyDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularRealFamilyDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularRealFamilyDiagonalEncodeBHist h

def regularRealFamilyDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularRealFamilyDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularRealFamilyDiagonalDecodeBHist tail)

private theorem RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularRealFamilyDiagonalDecodeBHist
      (regularRealFamilyDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularRealFamilyDiagonalToEventFlow : RegularRealFamilyDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularRealFamilyDiagonalUp.mk S R D Z E H C P N =>
      [[BMark.b0],
        regularRealFamilyDiagonalEncodeBHist S,
        [BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularRealFamilyDiagonalEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularRealFamilyDiagonalEncodeBHist N]

private def regularRealFamilyDiagonalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularRealFamilyDiagonalEventAtDefault index rest

def regularRealFamilyDiagonalFromEventFlow (ef : EventFlow) :
    Option RegularRealFamilyDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularRealFamilyDiagonalUp.mk
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 1 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 3 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 5 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 7 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 9 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 11 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 13 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 15 ef))
      (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEventAtDefault 17 ef)))

private theorem RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularRealFamilyDiagonalUp,
      regularRealFamilyDiagonalFromEventFlow
        (regularRealFamilyDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D Z E H C P N =>
      change
        some
            (RegularRealFamilyDiagonalUp.mk
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist S))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist R))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist D))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist Z))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist E))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist H))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist C))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist P))
              (regularRealFamilyDiagonalDecodeBHist (regularRealFamilyDiagonalEncodeBHist N))) =
          some (RegularRealFamilyDiagonalUp.mk S R D Z E H C P N)
      rw [RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode S,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode R,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode D,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode Z,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode E,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode H,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode C,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode P,
        RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularRealFamilyDiagonalToEventFlow_injective
    {x y : RegularRealFamilyDiagonalUp} :
    regularRealFamilyDiagonalToEventFlow x =
      regularRealFamilyDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularRealFamilyDiagonalFromEventFlow (regularRealFamilyDiagonalToEventFlow x) =
        regularRealFamilyDiagonalFromEventFlow (regularRealFamilyDiagonalToEventFlow y) :=
    congrArg regularRealFamilyDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_round_trip y)))

instance regularRealFamilyDiagonalBHistCarrier :
    BHistCarrier RegularRealFamilyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularRealFamilyDiagonalToEventFlow
  fromEventFlow := regularRealFamilyDiagonalFromEventFlow

instance regularRealFamilyDiagonalChapterTasteGate :
    ChapterTasteGate RegularRealFamilyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularRealFamilyDiagonalFromEventFlow
      (regularRealFamilyDiagonalToEventFlow x) = some x
    exact RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularRealFamilyDiagonalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularRealFamilyDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularRealFamilyDiagonalChapterTasteGate

theorem RegularRealFamilyDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularRealFamilyDiagonalDecodeBHist
      (regularRealFamilyDiagonalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularRealFamilyDiagonalUp) ∧
        Nonempty (ChapterTasteGate RegularRealFamilyDiagonalUp) ∧
          regularRealFamilyDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularRealFamilyDiagonalTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularRealFamilyDiagonalBHistCarrier⟩,
      ⟨regularRealFamilyDiagonalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularRealFamilyDiagonalUp
