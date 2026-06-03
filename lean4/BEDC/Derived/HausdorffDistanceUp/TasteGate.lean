import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffDistanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffDistanceUp : Type where
  | mk (A B H NX NY D E R T C P L : BHist) : HausdorffDistanceUp
  deriving DecidableEq

def hausdorffDistanceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffDistanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffDistanceEncodeBHist h

def hausdorffDistanceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffDistanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffDistanceDecodeBHist tail)

private theorem HausdorffDistanceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffDistanceFields : HausdorffDistanceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffDistanceUp.mk A B H NX NY D E R T C P L => [A, B, H, NX, NY, D, E, R, T, C, P, L]

def hausdorffDistanceToEventFlow : HausdorffDistanceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hausdorffDistanceFields x).map hausdorffDistanceEncodeBHist

private def hausdorffDistanceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffDistanceEventAtDefault index rest

def hausdorffDistanceFromEventFlow (ef : EventFlow) : Option HausdorffDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffDistanceUp.mk
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 0 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 1 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 2 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 3 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 4 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 5 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 6 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 7 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 8 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 9 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 10 ef))
      (hausdorffDistanceDecodeBHist (hausdorffDistanceEventAtDefault 11 ef)))

private theorem HausdorffDistanceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffDistanceUp,
      hausdorffDistanceFromEventFlow (hausdorffDistanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B H NX NY D E R T C P L =>
      change
        some
          (HausdorffDistanceUp.mk
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist A))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist B))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist H))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist NX))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist NY))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist D))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist E))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist R))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist T))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist C))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist P))
            (hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist L))) =
          some (HausdorffDistanceUp.mk A B H NX NY D E R T C P L)
      rw [HausdorffDistanceTasteGate_single_carrier_alignment_decode A,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode B,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode H,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode NX,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode NY,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode D,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode E,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode R,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode T,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode C,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode P,
        HausdorffDistanceTasteGate_single_carrier_alignment_decode L]

private theorem HausdorffDistanceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffDistanceUp} :
    hausdorffDistanceToEventFlow x = hausdorffDistanceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = hausdorffDistanceFromEventFlow (hausdorffDistanceToEventFlow x) :=
        (HausdorffDistanceTasteGate_single_carrier_alignment_round_trip x).symm
      _ = hausdorffDistanceFromEventFlow (hausdorffDistanceToEventFlow y) :=
        congrArg hausdorffDistanceFromEventFlow hxy
      _ = some y := HausdorffDistanceTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem HausdorffDistanceTasteGate_single_carrier_alignment_fields :
    ∀ x y : HausdorffDistanceUp, hausdorffDistanceFields x = hausdorffDistanceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 B1 H1 NX1 NY1 D1 E1 R1 T1 C1 P1 L1 =>
      cases y with
      | mk A2 B2 H2 NX2 NY2 D2 E2 R2 T2 C2 P2 L2 =>
          cases hfields
          rfl

instance hausdorffDistanceBHistCarrier : BHistCarrier HausdorffDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffDistanceToEventFlow
  fromEventFlow := hausdorffDistanceFromEventFlow

instance hausdorffDistanceChapterTasteGate : ChapterTasteGate HausdorffDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffDistanceFromEventFlow (hausdorffDistanceToEventFlow x) = some x
    exact HausdorffDistanceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffDistanceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hausdorffDistanceFieldFaithful : FieldFaithful HausdorffDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffDistanceFields
  field_faithful := HausdorffDistanceTasteGate_single_carrier_alignment_fields

instance hausdorffDistanceNontrivial : Nontrivial HausdorffDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffDistanceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffDistanceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffDistanceChapterTasteGate

theorem HausdorffDistanceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HausdorffDistanceUp) ∧
      Nonempty (FieldFaithful HausdorffDistanceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HausdorffDistanceUp) ∧
          (∀ h : BHist,
            hausdorffDistanceDecodeBHist (hausdorffDistanceEncodeBHist h) = h) ∧
            (∀ x : HausdorffDistanceUp,
              hausdorffDistanceFromEventFlow (hausdorffDistanceToEventFlow x) = some x) ∧
              (∀ x y : HausdorffDistanceUp,
                hausdorffDistanceToEventFlow x = hausdorffDistanceToEventFlow y -> x = y) ∧
                hausdorffDistanceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨hausdorffDistanceChapterTasteGate⟩,
      ⟨hausdorffDistanceFieldFaithful⟩,
      ⟨hausdorffDistanceNontrivial⟩,
      HausdorffDistanceTasteGate_single_carrier_alignment_decode,
      HausdorffDistanceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HausdorffDistanceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HausdorffDistanceUp
