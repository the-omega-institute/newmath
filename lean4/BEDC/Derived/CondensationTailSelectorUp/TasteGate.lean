import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CondensationTailSelectorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CondensationTailSelectorUp : Type where
  | mk (K A D M S R E H C P N : BHist) : CondensationTailSelectorUp
  deriving DecidableEq

def condensationTailSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: condensationTailSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: condensationTailSelectorEncodeBHist h

def condensationTailSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (condensationTailSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (condensationTailSelectorDecodeBHist tail)

private theorem CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def condensationTailSelectorToEventFlow : CondensationTailSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CondensationTailSelectorUp.mk K A D M S R E H C P N =>
      [[BMark.b0],
        condensationTailSelectorEncodeBHist K,
        [BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        condensationTailSelectorEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        condensationTailSelectorEncodeBHist N]

private def condensationTailSelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => condensationTailSelectorEventAtDefault index rest

def condensationTailSelectorFromEventFlow (ef : EventFlow) : Option CondensationTailSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CondensationTailSelectorUp.mk
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 1 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 3 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 5 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 7 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 9 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 11 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 13 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 15 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 17 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 19 ef))
      (condensationTailSelectorDecodeBHist (condensationTailSelectorEventAtDefault 21 ef)))

private theorem CondensationTailSelectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CondensationTailSelectorUp,
      condensationTailSelectorFromEventFlow (condensationTailSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K A D M S R E H C P N =>
      change
        some
          (CondensationTailSelectorUp.mk
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist K))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist A))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist D))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist M))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist S))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist R))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist E))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist H))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist C))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist P))
            (condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist N))) =
          some (CondensationTailSelectorUp.mk K A D M S R E H C P N)
      rw [CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode K,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode A,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode D,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode M,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode S,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode R,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode E,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode H,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode C,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode P,
        CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode N]

private theorem CondensationTailSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CondensationTailSelectorUp} :
    condensationTailSelectorToEventFlow x = condensationTailSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      condensationTailSelectorFromEventFlow (condensationTailSelectorToEventFlow x) =
        condensationTailSelectorFromEventFlow (condensationTailSelectorToEventFlow y) :=
    congrArg condensationTailSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CondensationTailSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CondensationTailSelectorTasteGate_single_carrier_alignment_round_trip y)))

instance condensationTailSelectorBHistCarrier : BHistCarrier CondensationTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := condensationTailSelectorToEventFlow
  fromEventFlow := condensationTailSelectorFromEventFlow

instance condensationTailSelectorChapterTasteGate :
    ChapterTasteGate CondensationTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change condensationTailSelectorFromEventFlow (condensationTailSelectorToEventFlow x) = some x
    exact CondensationTailSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CondensationTailSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CondensationTailSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  condensationTailSelectorChapterTasteGate

theorem CondensationTailSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist, condensationTailSelectorDecodeBHist (condensationTailSelectorEncodeBHist h) = h) ∧
      (∀ x : CondensationTailSelectorUp,
        condensationTailSelectorFromEventFlow (condensationTailSelectorToEventFlow x) = some x) ∧
        (∀ x y : CondensationTailSelectorUp,
          condensationTailSelectorToEventFlow x = condensationTailSelectorToEventFlow y → x = y) ∧
          condensationTailSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CondensationTailSelectorTasteGate_single_carrier_alignment_decode_encode,
      CondensationTailSelectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CondensationTailSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CondensationTailSelectorUp.TasteGate
