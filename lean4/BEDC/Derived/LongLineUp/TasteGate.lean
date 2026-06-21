import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LongLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LongLineUp : Type where
  | mk (S I O T H C P N : BHist) : LongLineUp
  deriving DecidableEq

def longLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: longLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: longLineEncodeBHist h

def longLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (longLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (longLineDecodeBHist tail)

private theorem LongLineTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, longLineDecodeBHist (longLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def longLineFields : LongLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LongLineUp.mk S I O T H C P N => [S, I, O, T, H, C, P, N]

def longLineToEventFlow : LongLineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (longLineFields x).map longLineEncodeBHist

private def longLineEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => longLineEventAtDefault index rest

def longLineFromEventFlow (ef : EventFlow) : Option LongLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LongLineUp.mk
      (longLineDecodeBHist (longLineEventAtDefault 0 ef))
      (longLineDecodeBHist (longLineEventAtDefault 1 ef))
      (longLineDecodeBHist (longLineEventAtDefault 2 ef))
      (longLineDecodeBHist (longLineEventAtDefault 3 ef))
      (longLineDecodeBHist (longLineEventAtDefault 4 ef))
      (longLineDecodeBHist (longLineEventAtDefault 5 ef))
      (longLineDecodeBHist (longLineEventAtDefault 6 ef))
      (longLineDecodeBHist (longLineEventAtDefault 7 ef)))

private theorem LongLineTasteGate_single_carrier_alignment_round_trip
    (x : LongLineUp) :
    longLineFromEventFlow (longLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S I O T H C P N =>
      change
        some
          (LongLineUp.mk
            (longLineDecodeBHist (longLineEncodeBHist S))
            (longLineDecodeBHist (longLineEncodeBHist I))
            (longLineDecodeBHist (longLineEncodeBHist O))
            (longLineDecodeBHist (longLineEncodeBHist T))
            (longLineDecodeBHist (longLineEncodeBHist H))
            (longLineDecodeBHist (longLineEncodeBHist C))
            (longLineDecodeBHist (longLineEncodeBHist P))
            (longLineDecodeBHist (longLineEncodeBHist N))) =
          some (LongLineUp.mk S I O T H C P N)
      rw [LongLineTasteGate_single_carrier_alignment_decode_encode S,
        LongLineTasteGate_single_carrier_alignment_decode_encode I,
        LongLineTasteGate_single_carrier_alignment_decode_encode O,
        LongLineTasteGate_single_carrier_alignment_decode_encode T,
        LongLineTasteGate_single_carrier_alignment_decode_encode H,
        LongLineTasteGate_single_carrier_alignment_decode_encode C,
        LongLineTasteGate_single_carrier_alignment_decode_encode P,
        LongLineTasteGate_single_carrier_alignment_decode_encode N]

private theorem LongLineTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LongLineUp} :
    longLineToEventFlow x = longLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      longLineFromEventFlow (longLineToEventFlow x) =
        longLineFromEventFlow (longLineToEventFlow y) :=
    congrArg longLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LongLineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LongLineTasteGate_single_carrier_alignment_round_trip y)))

instance longLineBHistCarrier : BHistCarrier LongLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := longLineToEventFlow
  fromEventFlow := longLineFromEventFlow

instance longLineChapterTasteGate : ChapterTasteGate LongLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change longLineFromEventFlow (longLineToEventFlow x) = some x
    exact LongLineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LongLineTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LongLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  longLineChapterTasteGate

theorem LongLineTasteGate_single_carrier_alignment :
    (∀ h : BHist, longLineDecodeBHist (longLineEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LongLineUp) ∧
        Nonempty (ChapterTasteGate LongLineUp) ∧
          longLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LongLineTasteGate_single_carrier_alignment_decode_encode,
      ⟨longLineBHistCarrier⟩,
      ⟨longLineChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LongLineUp
