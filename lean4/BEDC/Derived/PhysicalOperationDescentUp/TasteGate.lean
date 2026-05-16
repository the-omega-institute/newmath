import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalOperationDescentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalOperationDescentUp : Type where
  | mk (O S E R F H C P N : BHist) : PhysicalOperationDescentUp
  deriving DecidableEq

def physicalOperationDescentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalOperationDescentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalOperationDescentEncodeBHist h

def physicalOperationDescentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalOperationDescentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalOperationDescentDecodeBHist tail)

private theorem physicalOperationDescentDecode_encode_bhist :
    ∀ h : BHist,
      physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def physicalOperationDescentFields : PhysicalOperationDescentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalOperationDescentUp.mk O S E R F H C P N => [O, S, E, R, F, H, C, P, N]

def physicalOperationDescentToEventFlow : PhysicalOperationDescentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalOperationDescentUp.mk O S E R F H C P N =>
      [[BMark.b0],
        physicalOperationDescentEncodeBHist O,
        [BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicalOperationDescentEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicalOperationDescentEncodeBHist N]

private def physicalOperationDescentRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => physicalOperationDescentRawAt n rest

private def physicalOperationDescentLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => physicalOperationDescentLengthEq n rest

def physicalOperationDescentFromEventFlow :
    EventFlow → Option PhysicalOperationDescentUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match physicalOperationDescentLengthEq 18 flow with
      | true =>
          some
            (PhysicalOperationDescentUp.mk
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 1 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 3 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 5 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 7 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 9 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 11 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 13 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 15 flow))
              (physicalOperationDescentDecodeBHist (physicalOperationDescentRawAt 17 flow)))
      | false => none

private theorem physicalOperationDescent_round_trip :
    ∀ x : PhysicalOperationDescentUp,
      physicalOperationDescentFromEventFlow
        (physicalOperationDescentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O S E R F H C P N =>
      change
        some
          (PhysicalOperationDescentUp.mk
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist O))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist S))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist E))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist R))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist F))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist H))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist C))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist P))
            (physicalOperationDescentDecodeBHist (physicalOperationDescentEncodeBHist N))) =
          some (PhysicalOperationDescentUp.mk O S E R F H C P N)
      rw [physicalOperationDescentDecode_encode_bhist O,
        physicalOperationDescentDecode_encode_bhist S,
        physicalOperationDescentDecode_encode_bhist E,
        physicalOperationDescentDecode_encode_bhist R,
        physicalOperationDescentDecode_encode_bhist F,
        physicalOperationDescentDecode_encode_bhist H,
        physicalOperationDescentDecode_encode_bhist C,
        physicalOperationDescentDecode_encode_bhist P,
        physicalOperationDescentDecode_encode_bhist N]

private theorem physicalOperationDescentToEventFlow_injective
    {x y : PhysicalOperationDescentUp} :
    physicalOperationDescentToEventFlow x =
        physicalOperationDescentToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalOperationDescentFromEventFlow
          (physicalOperationDescentToEventFlow x) =
        physicalOperationDescentFromEventFlow
          (physicalOperationDescentToEventFlow y) :=
    congrArg physicalOperationDescentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalOperationDescent_round_trip x).symm
      (Eq.trans hread (physicalOperationDescent_round_trip y)))

private theorem physicalOperationDescent_field_faithful :
    ∀ x y : PhysicalOperationDescentUp,
      physicalOperationDescentFields x = physicalOperationDescentFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 S1 E1 R1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 S2 E2 R2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance physicalOperationDescentBHistCarrier :
    BHistCarrier PhysicalOperationDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalOperationDescentToEventFlow
  fromEventFlow := physicalOperationDescentFromEventFlow

instance physicalOperationDescentChapterTasteGate :
    ChapterTasteGate PhysicalOperationDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      physicalOperationDescentFromEventFlow
        (physicalOperationDescentToEventFlow x) = some x
    exact physicalOperationDescent_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalOperationDescentToEventFlow_injective heq)

instance physicalOperationDescentFieldFaithful :
    FieldFaithful PhysicalOperationDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalOperationDescentFields
  field_faithful := physicalOperationDescent_field_faithful

instance physicalOperationDescentNontrivial :
    Nontrivial PhysicalOperationDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalOperationDescentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalOperationDescentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalOperationDescentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalOperationDescentChapterTasteGate

namespace TasteGate

theorem PhysicalOperationDescentTasteGate_single_carrier_alignment :
    (physicalOperationDescentEncodeBHist BHist.Empty = ([] : List BMark)) ∧
      (∀ h : BHist,
        physicalOperationDescentDecodeBHist
          (physicalOperationDescentEncodeBHist h) = h) ∧
        (∀ x : PhysicalOperationDescentUp,
          physicalOperationDescentFromEventFlow
            (physicalOperationDescentToEventFlow x) = some x) ∧
          (∀ x y : PhysicalOperationDescentUp,
            physicalOperationDescentToEventFlow x =
                physicalOperationDescentToEventFlow y →
              x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl,
      physicalOperationDescentDecode_encode_bhist,
      physicalOperationDescent_round_trip,
      (fun _ _ heq => physicalOperationDescentToEventFlow_injective heq)⟩

end TasteGate

end BEDC.Derived.PhysicalOperationDescentUp
