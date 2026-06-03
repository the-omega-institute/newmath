import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequenceSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequenceSpaceUp : Type where
  | mk (S R D E K H C P N : BHist) : RealSequenceSpaceUp
  deriving DecidableEq

def realSequenceSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSequenceSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSequenceSpaceEncodeBHist h

def realSequenceSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSequenceSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSequenceSpaceDecodeBHist tail)

private theorem RealSequenceSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSequenceSpaceToEventFlow : RealSequenceSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceSpaceUp.mk S R D E K H C P N =>
      [realSequenceSpaceEncodeBHist S,
        realSequenceSpaceEncodeBHist R,
        realSequenceSpaceEncodeBHist D,
        realSequenceSpaceEncodeBHist E,
        realSequenceSpaceEncodeBHist K,
        realSequenceSpaceEncodeBHist H,
        realSequenceSpaceEncodeBHist C,
        realSequenceSpaceEncodeBHist P,
        realSequenceSpaceEncodeBHist N]

private def realSequenceSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realSequenceSpaceEventAtDefault index rest

def realSequenceSpaceFromEventFlow (ef : EventFlow) : Option RealSequenceSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealSequenceSpaceUp.mk
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 0 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 1 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 2 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 3 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 4 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 5 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 6 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 7 ef))
      (realSequenceSpaceDecodeBHist (realSequenceSpaceEventAtDefault 8 ef)))

private theorem RealSequenceSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealSequenceSpaceUp,
      realSequenceSpaceFromEventFlow (realSequenceSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D E K H C P N =>
      change
        some
            (RealSequenceSpaceUp.mk
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist S))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist R))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist D))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist E))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist K))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist H))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist C))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist P))
              (realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist N))) =
          some (RealSequenceSpaceUp.mk S R D E K H C P N)
      rw [RealSequenceSpaceTasteGate_single_carrier_alignment_decode S,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode R,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode D,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode E,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode K,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode H,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode C,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode P,
        RealSequenceSpaceTasteGate_single_carrier_alignment_decode N]

private theorem realSequenceSpaceToEventFlow_injective {x y : RealSequenceSpaceUp} :
    realSequenceSpaceToEventFlow x = realSequenceSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSequenceSpaceFromEventFlow (realSequenceSpaceToEventFlow x) =
        realSequenceSpaceFromEventFlow (realSequenceSpaceToEventFlow y) :=
    congrArg realSequenceSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealSequenceSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSequenceSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance realSequenceSpaceBHistCarrier : BHistCarrier RealSequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSequenceSpaceToEventFlow
  fromEventFlow := realSequenceSpaceFromEventFlow

instance realSequenceSpaceChapterTasteGate : ChapterTasteGate RealSequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSequenceSpaceFromEventFlow (realSequenceSpaceToEventFlow x) = some x
    exact RealSequenceSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSequenceSpaceToEventFlow_injective heq)

theorem RealSequenceSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSequenceSpaceDecodeBHist (realSequenceSpaceEncodeBHist h) = h) ∧
      (∀ x : RealSequenceSpaceUp,
        realSequenceSpaceFromEventFlow (realSequenceSpaceToEventFlow x) = some x) ∧
        (∀ x y : RealSequenceSpaceUp,
          realSequenceSpaceToEventFlow x = realSequenceSpaceToEventFlow y → x = y) ∧
          realSequenceSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealSequenceSpaceTasteGate_single_carrier_alignment_decode,
      RealSequenceSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => realSequenceSpaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealSequenceSpaceUp
