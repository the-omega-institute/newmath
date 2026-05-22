import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBudgetTailMeetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBudgetTailMeetUp : Type where
  | mk (B T L H C P N : BHist) : RealBudgetTailMeetUp
  deriving DecidableEq

def realBudgetTailMeetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBudgetTailMeetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBudgetTailMeetEncodeBHist h

def realBudgetTailMeetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBudgetTailMeetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBudgetTailMeetDecodeBHist tail)

private theorem RealBudgetTailMeetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBudgetTailMeetFields : RealBudgetTailMeetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBudgetTailMeetUp.mk B T L H C P N => [B, T, L, H, C, P, N]

def realBudgetTailMeetToEventFlow : RealBudgetTailMeetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realBudgetTailMeetFields x).map realBudgetTailMeetEncodeBHist

private def realBudgetTailMeetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realBudgetTailMeetEventAtDefault index rest

def realBudgetTailMeetFromEventFlow (ef : EventFlow) : Option RealBudgetTailMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealBudgetTailMeetUp.mk
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 0 ef))
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 1 ef))
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 2 ef))
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 3 ef))
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 4 ef))
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 5 ef))
      (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEventAtDefault 6 ef)))

private theorem RealBudgetTailMeetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealBudgetTailMeetUp,
      realBudgetTailMeetFromEventFlow (realBudgetTailMeetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B T L H C P N =>
      change
        some
            (RealBudgetTailMeetUp.mk
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist B))
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist T))
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist L))
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist H))
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist C))
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist P))
              (realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist N))) =
          some (RealBudgetTailMeetUp.mk B T L H C P N)
      rw [RealBudgetTailMeetTasteGate_single_carrier_alignment_decode B,
        RealBudgetTailMeetTasteGate_single_carrier_alignment_decode T,
        RealBudgetTailMeetTasteGate_single_carrier_alignment_decode L,
        RealBudgetTailMeetTasteGate_single_carrier_alignment_decode H,
        RealBudgetTailMeetTasteGate_single_carrier_alignment_decode C,
        RealBudgetTailMeetTasteGate_single_carrier_alignment_decode P,
        RealBudgetTailMeetTasteGate_single_carrier_alignment_decode N]

private theorem RealBudgetTailMeetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealBudgetTailMeetUp} :
    realBudgetTailMeetToEventFlow x = realBudgetTailMeetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBudgetTailMeetFromEventFlow (realBudgetTailMeetToEventFlow x) =
        realBudgetTailMeetFromEventFlow (realBudgetTailMeetToEventFlow y) :=
    congrArg realBudgetTailMeetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealBudgetTailMeetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealBudgetTailMeetTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealBudgetTailMeetTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealBudgetTailMeetUp, realBudgetTailMeetFields x = realBudgetTailMeetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 T1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 T2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realBudgetTailMeetBHistCarrier : BHistCarrier RealBudgetTailMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBudgetTailMeetToEventFlow
  fromEventFlow := realBudgetTailMeetFromEventFlow

instance realBudgetTailMeetChapterTasteGate : ChapterTasteGate RealBudgetTailMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBudgetTailMeetFromEventFlow (realBudgetTailMeetToEventFlow x) = some x
    exact RealBudgetTailMeetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealBudgetTailMeetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realBudgetTailMeetFieldFaithful : FieldFaithful RealBudgetTailMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realBudgetTailMeetFields
  field_faithful := RealBudgetTailMeetTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate RealBudgetTailMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realBudgetTailMeetChapterTasteGate

theorem RealBudgetTailMeetTasteGate_single_carrier_alignment :
    (∀ h : BHist, realBudgetTailMeetDecodeBHist (realBudgetTailMeetEncodeBHist h) = h) ∧
      (∀ x : RealBudgetTailMeetUp,
        realBudgetTailMeetFromEventFlow (realBudgetTailMeetToEventFlow x) = some x) ∧
        (∀ x y : RealBudgetTailMeetUp,
          realBudgetTailMeetToEventFlow x = realBudgetTailMeetToEventFlow y → x = y) ∧
          realBudgetTailMeetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨RealBudgetTailMeetTasteGate_single_carrier_alignment_decode,
      RealBudgetTailMeetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealBudgetTailMeetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealBudgetTailMeetUp
