import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisZeckendorfCarryBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisZeckendorfCarryBudgetUp : Type where
  | mk (h k G Nk V Q H C P N : BHist) : AxisZeckendorfCarryBudgetUp
  deriving DecidableEq

def axisZeckendorfCarryBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 tail => BMark.b0 :: axisZeckendorfCarryBudgetEncodeBHist tail
  | BHist.e1 tail => BMark.b1 :: axisZeckendorfCarryBudgetEncodeBHist tail

def axisZeckendorfCarryBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisZeckendorfCarryBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisZeckendorfCarryBudgetDecodeBHist tail)

private theorem AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode :
    ∀ row : BHist,
      axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEncodeBHist row) = row := by
  -- BEDC touchpoint anchor: BHist BMark
  intro row
  induction row with
  | Empty => rfl
  | e0 row ih => exact congrArg BHist.e0 ih
  | e1 row ih => exact congrArg BHist.e1 ih

def axisZeckendorfCarryBudgetToEventFlow : AxisZeckendorfCarryBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisZeckendorfCarryBudgetUp.mk h k G Nk V Q H C P N =>
      [axisZeckendorfCarryBudgetEncodeBHist h,
        axisZeckendorfCarryBudgetEncodeBHist k,
        axisZeckendorfCarryBudgetEncodeBHist G,
        axisZeckendorfCarryBudgetEncodeBHist Nk,
        axisZeckendorfCarryBudgetEncodeBHist V,
        axisZeckendorfCarryBudgetEncodeBHist Q,
        axisZeckendorfCarryBudgetEncodeBHist H,
        axisZeckendorfCarryBudgetEncodeBHist C,
        axisZeckendorfCarryBudgetEncodeBHist P,
        axisZeckendorfCarryBudgetEncodeBHist N]

private def axisZeckendorfCarryBudgetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      axisZeckendorfCarryBudgetEventAtDefault index rest

def axisZeckendorfCarryBudgetFromEventFlow
    (flow : EventFlow) : Option AxisZeckendorfCarryBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AxisZeckendorfCarryBudgetUp.mk
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 0 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 1 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 2 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 3 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 4 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 5 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 6 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 7 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 8 flow))
      (axisZeckendorfCarryBudgetDecodeBHist
        (axisZeckendorfCarryBudgetEventAtDefault 9 flow)))

private theorem AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_round_trip
    (x : AxisZeckendorfCarryBudgetUp) :
    axisZeckendorfCarryBudgetFromEventFlow
      (axisZeckendorfCarryBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk h k G Nk V Q H C P N =>
      change
        some
          (AxisZeckendorfCarryBudgetUp.mk
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist h))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist k))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist G))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist Nk))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist V))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist Q))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist H))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist C))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist P))
            (axisZeckendorfCarryBudgetDecodeBHist
              (axisZeckendorfCarryBudgetEncodeBHist N))) =
          some (AxisZeckendorfCarryBudgetUp.mk h k G Nk V Q H C P N)
      rw [AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode h,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode k,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode G,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode Nk,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode V,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode Q,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode H,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode C,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode P,
        AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_decode_encode N]

private theorem AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AxisZeckendorfCarryBudgetUp} :
    axisZeckendorfCarryBudgetToEventFlow x =
      axisZeckendorfCarryBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisZeckendorfCarryBudgetFromEventFlow
          (axisZeckendorfCarryBudgetToEventFlow x) =
        axisZeckendorfCarryBudgetFromEventFlow
          (axisZeckendorfCarryBudgetToEventFlow y) :=
    congrArg axisZeckendorfCarryBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_round_trip y)))

instance axisZeckendorfCarryBudgetBHistCarrier :
    BHistCarrier AxisZeckendorfCarryBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisZeckendorfCarryBudgetToEventFlow
  fromEventFlow := axisZeckendorfCarryBudgetFromEventFlow

instance axisZeckendorfCarryBudgetChapterTasteGate :
    ChapterTasteGate AxisZeckendorfCarryBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      axisZeckendorfCarryBudgetFromEventFlow
        (axisZeckendorfCarryBudgetToEventFlow x) = some x
    exact AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AxisZeckendorfCarryBudgetTasteGate_single_carrier_alignment :
    ChapterTasteGate AxisZeckendorfCarryBudgetUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact axisZeckendorfCarryBudgetChapterTasteGate

end BEDC.Derived.AxisZeckendorfCarryBudgetUp
