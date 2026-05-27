import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalDistanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalDistanceUp : Type where
  | mk (X I K A T S R H C P N : BHist) : RealIntervalDistanceUp
  deriving DecidableEq

def realIntervalDistanceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalDistanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalDistanceEncodeBHist h

def realIntervalDistanceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalDistanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalDistanceDecodeBHist tail)

private theorem RealIntervalDistanceTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalDistanceFields : RealIntervalDistanceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalDistanceUp.mk X I K A T S R H C P N => [X, I, K, A, T, S, R, H, C, P, N]

def realIntervalDistanceToEventFlow : RealIntervalDistanceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realIntervalDistanceFields x).map realIntervalDistanceEncodeBHist

private def realIntervalDistanceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realIntervalDistanceEventAtDefault index rest

def realIntervalDistanceFromEventFlow (ef : EventFlow) : Option RealIntervalDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalDistanceUp.mk
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 0 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 1 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 2 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 3 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 4 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 5 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 6 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 7 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 8 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 9 ef))
      (realIntervalDistanceDecodeBHist (realIntervalDistanceEventAtDefault 10 ef)))

private theorem RealIntervalDistanceTasteGate_single_carrier_alignment_round_trip :
    forall x : RealIntervalDistanceUp,
      realIntervalDistanceFromEventFlow (realIntervalDistanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X I K A T S R H C P N =>
      change
        some
          (RealIntervalDistanceUp.mk
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist X))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist I))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist K))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist A))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist T))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist S))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist R))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist H))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist C))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist P))
            (realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist N))) =
          some (RealIntervalDistanceUp.mk X I K A T S R H C P N)
      rw [RealIntervalDistanceTasteGate_single_carrier_alignment_decode X,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode I,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode K,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode A,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode T,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode S,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode R,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode H,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode C,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode P,
        RealIntervalDistanceTasteGate_single_carrier_alignment_decode N]

private theorem RealIntervalDistanceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealIntervalDistanceUp} :
    realIntervalDistanceToEventFlow x = realIntervalDistanceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalDistanceFromEventFlow (realIntervalDistanceToEventFlow x) =
        realIntervalDistanceFromEventFlow (realIntervalDistanceToEventFlow y) :=
    congrArg realIntervalDistanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealIntervalDistanceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealIntervalDistanceTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealIntervalDistanceTasteGate_single_carrier_alignment_fields :
    forall x y : RealIntervalDistanceUp, realIntervalDistanceFields x = realIntervalDistanceFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 I1 K1 A1 T1 S1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 I2 K2 A2 T2 S2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realIntervalDistanceBHistCarrier : BHistCarrier RealIntervalDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalDistanceToEventFlow
  fromEventFlow := realIntervalDistanceFromEventFlow

instance realIntervalDistanceChapterTasteGate : ChapterTasteGate RealIntervalDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalDistanceFromEventFlow (realIntervalDistanceToEventFlow x) = some x
    exact RealIntervalDistanceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealIntervalDistanceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realIntervalDistanceFieldFaithful : FieldFaithful RealIntervalDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realIntervalDistanceFields
  field_faithful := RealIntervalDistanceTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate RealIntervalDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntervalDistanceChapterTasteGate

theorem RealIntervalDistanceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealIntervalDistanceUp) ∧
      Nonempty (FieldFaithful RealIntervalDistanceUp) ∧
        (∀ h : BHist, realIntervalDistanceDecodeBHist (realIntervalDistanceEncodeBHist h) = h) ∧
          realIntervalDistanceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨realIntervalDistanceChapterTasteGate⟩, ⟨realIntervalDistanceFieldFaithful⟩,
      RealIntervalDistanceTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.RealIntervalDistanceUp
