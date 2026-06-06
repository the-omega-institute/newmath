import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitSpaceUp : Type where
  | mk (F S D R L0 H C P N : BHist) : LimitSpaceUp
  deriving DecidableEq

def limitSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitSpaceEncodeBHist h

def limitSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitSpaceDecodeBHist tail)

private theorem LimitSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, limitSpaceDecodeBHist (limitSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limitSpaceToEventFlow : LimitSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LimitSpaceUp.mk F S D R L0 H C P N =>
      [[BMark.b0],
        limitSpaceEncodeBHist F,
        [BMark.b1, BMark.b0],
        limitSpaceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        limitSpaceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        limitSpaceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        limitSpaceEncodeBHist L0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        limitSpaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        limitSpaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        limitSpaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        limitSpaceEncodeBHist N]

private def limitSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => limitSpaceEventAtDefault index rest

def limitSpaceFromEventFlow (ef : EventFlow) : Option LimitSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LimitSpaceUp.mk
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 1 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 3 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 5 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 7 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 9 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 11 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 13 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 15 ef))
      (limitSpaceDecodeBHist (limitSpaceEventAtDefault 17 ef)))

private theorem LimitSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LimitSpaceUp, limitSpaceFromEventFlow (limitSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S D R L0 H C P N =>
      change
        some
          (LimitSpaceUp.mk
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist F))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist S))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist D))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist R))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist L0))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist H))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist C))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist P))
            (limitSpaceDecodeBHist (limitSpaceEncodeBHist N))) =
          some (LimitSpaceUp.mk F S D R L0 H C P N)
      rw [LimitSpaceTasteGate_single_carrier_alignment_decode_encode F,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode S,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode D,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode R,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode L0,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode H,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode C,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode P,
        LimitSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem LimitSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LimitSpaceUp} :
    limitSpaceToEventFlow x = limitSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitSpaceFromEventFlow (limitSpaceToEventFlow x) =
        limitSpaceFromEventFlow (limitSpaceToEventFlow y) :=
    congrArg limitSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LimitSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LimitSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance limitSpaceBHistCarrier : BHistCarrier LimitSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitSpaceToEventFlow
  fromEventFlow := limitSpaceFromEventFlow

instance limitSpaceChapterTasteGate : ChapterTasteGate LimitSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitSpaceFromEventFlow (limitSpaceToEventFlow x) = some x
    exact LimitSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LimitSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LimitSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  limitSpaceChapterTasteGate

theorem LimitSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, limitSpaceDecodeBHist (limitSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LimitSpaceUp) ∧
        Nonempty (ChapterTasteGate LimitSpaceUp) ∧
          limitSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LimitSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨limitSpaceBHistCarrier⟩,
      ⟨limitSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LimitSpaceUp
