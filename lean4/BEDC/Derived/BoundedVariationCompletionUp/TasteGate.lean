import BEDC.Derived.BoundedVariationCompletionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedVariationCompletionUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def boundedVariationCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedVariationCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedVariationCompletionEncodeBHist h

def boundedVariationCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedVariationCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedVariationCompletionDecodeBHist tail)

private theorem BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedVariationCompletionFields : BoundedVariationCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedVariationCompletionUp.mk V R D I S Q E H C P N => [V, R, D, I, S, Q, E, H, C, P, N]

def boundedVariationCompletionToEventFlow : BoundedVariationCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedVariationCompletionFields x).map boundedVariationCompletionEncodeBHist

private def boundedVariationCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedVariationCompletionEventAtDefault index rest

def boundedVariationCompletionFromEventFlow (ef : EventFlow) : Option BoundedVariationCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedVariationCompletionUp.mk
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 0 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 1 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 2 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 3 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 4 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 5 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 6 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 7 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 8 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 9 ef))
      (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEventAtDefault 10 ef)))

private theorem BoundedVariationCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedVariationCompletionUp,
      boundedVariationCompletionFromEventFlow (boundedVariationCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V R D I S Q E H C P N =>
      change
        some
          (BoundedVariationCompletionUp.mk
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist V))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist R))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist D))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist I))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist S))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist Q))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist E))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist H))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist C))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist P))
            (boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist N))) =
          some (BoundedVariationCompletionUp.mk V R D I S Q E H C P N)
      rw [BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode V,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode I,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedVariationCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedVariationCompletionUp} :
    boundedVariationCompletionToEventFlow x = boundedVariationCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedVariationCompletionFromEventFlow (boundedVariationCompletionToEventFlow x) =
        boundedVariationCompletionFromEventFlow (boundedVariationCompletionToEventFlow y) :=
    congrArg boundedVariationCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedVariationCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedVariationCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedVariationCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundedVariationCompletionUp,
      boundedVariationCompletionFields x = boundedVariationCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 R1 D1 I1 S1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk V2 R2 D2 I2 S2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance boundedVariationCompletionBHistCarrier : BHistCarrier BoundedVariationCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedVariationCompletionToEventFlow
  fromEventFlow := boundedVariationCompletionFromEventFlow

instance boundedVariationCompletionChapterTasteGate :
    ChapterTasteGate BoundedVariationCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedVariationCompletionFromEventFlow (boundedVariationCompletionToEventFlow x) =
      some x
    exact BoundedVariationCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedVariationCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedVariationCompletionFieldFaithful :
    FieldFaithful BoundedVariationCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedVariationCompletionFields
  field_faithful := BoundedVariationCompletionTasteGate_single_carrier_alignment_fields

instance boundedVariationCompletionNontrivial :
    Nontrivial BoundedVariationCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedVariationCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedVariationCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedVariationCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedVariationCompletionUp) ∧
      Nonempty (FieldFaithful BoundedVariationCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedVariationCompletionUp) ∧
          (∀ h : BHist,
            boundedVariationCompletionDecodeBHist (boundedVariationCompletionEncodeBHist h) = h) ∧
            (∀ x : BoundedVariationCompletionUp,
              boundedVariationCompletionFromEventFlow (boundedVariationCompletionToEventFlow x) =
                some x) ∧
              (∀ x y : BoundedVariationCompletionUp,
                boundedVariationCompletionToEventFlow x = boundedVariationCompletionToEventFlow y →
                  x = y) ∧
                boundedVariationCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨boundedVariationCompletionChapterTasteGate⟩,
      ⟨boundedVariationCompletionFieldFaithful⟩,
      ⟨boundedVariationCompletionNontrivial⟩,
      BoundedVariationCompletionTasteGate_single_carrier_alignment_decode_encode,
      BoundedVariationCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedVariationCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedVariationCompletionUp
