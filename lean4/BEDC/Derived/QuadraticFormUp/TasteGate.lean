import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuadraticFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuadraticFormUp : Type where
  | mk (F V B q H P T C S N : BHist) : QuadraticFormUp
  deriving DecidableEq

def quadraticFormEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quadraticFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quadraticFormEncodeBHist h

def quadraticFormDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quadraticFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quadraticFormDecodeBHist tail)

private theorem QuadraticFormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, quadraticFormDecodeBHist (quadraticFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quadraticFormFields : QuadraticFormUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | QuadraticFormUp.mk F V B q H P T C S N => [F, V, B, q, H, P, T, C, S, N]

def quadraticFormToEventFlow : QuadraticFormUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (quadraticFormFields x).map quadraticFormEncodeBHist

private def quadraticFormEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => quadraticFormEventAt index rest

def quadraticFormFromEventFlow (ef : EventFlow) : Option QuadraticFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (QuadraticFormUp.mk
      (quadraticFormDecodeBHist (quadraticFormEventAt 0 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 1 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 2 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 3 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 4 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 5 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 6 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 7 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 8 ef))
      (quadraticFormDecodeBHist (quadraticFormEventAt 9 ef)))

private theorem QuadraticFormTasteGate_single_carrier_alignment_round_trip
    (x : QuadraticFormUp) :
    quadraticFormFromEventFlow (quadraticFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F V B q H P T C S N =>
      change
        some
          (QuadraticFormUp.mk
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist F))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist V))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist B))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist q))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist H))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist P))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist T))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist C))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist S))
            (quadraticFormDecodeBHist (quadraticFormEncodeBHist N))) =
          some (QuadraticFormUp.mk F V B q H P T C S N)
      rw [QuadraticFormTasteGate_single_carrier_alignment_decode_encode F,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode V,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode B,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode q,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode H,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode P,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode T,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode C,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode S,
        QuadraticFormTasteGate_single_carrier_alignment_decode_encode N]

private theorem QuadraticFormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : QuadraticFormUp} :
    quadraticFormToEventFlow x = quadraticFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quadraticFormFromEventFlow (quadraticFormToEventFlow x) =
        quadraticFormFromEventFlow (quadraticFormToEventFlow y) :=
    congrArg quadraticFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (QuadraticFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (QuadraticFormTasteGate_single_carrier_alignment_round_trip y)))

private theorem QuadraticFormTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : QuadraticFormUp, quadraticFormFields x = quadraticFormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ V₁ B₁ q₁ H₁ P₁ T₁ C₁ S₁ N₁ =>
      cases y with
      | mk F₂ V₂ B₂ q₂ H₂ P₂ T₂ C₂ S₂ N₂ =>
          cases hfields
          rfl

instance quadraticFormBHistCarrier : BHistCarrier QuadraticFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quadraticFormToEventFlow
  fromEventFlow := quadraticFormFromEventFlow

instance quadraticFormChapterTasteGate : ChapterTasteGate QuadraticFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quadraticFormFromEventFlow (quadraticFormToEventFlow x) = some x
    exact QuadraticFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (QuadraticFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance quadraticFormFieldFaithful : FieldFaithful QuadraticFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := quadraticFormFields
  field_faithful := QuadraticFormTasteGate_single_carrier_alignment_fields_faithful

instance quadraticFormNontrivial : Nontrivial QuadraticFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuadraticFormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuadraticFormUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def QuadraticFormTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate QuadraticFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quadraticFormChapterTasteGate

theorem QuadraticFormTasteGate_single_carrier_alignment :
    (∀ h : BHist, quadraticFormDecodeBHist (quadraticFormEncodeBHist h) = h) ∧
      (∀ x : QuadraticFormUp,
        quadraticFormFromEventFlow (quadraticFormToEventFlow x) = some x) ∧
        (∀ x y : QuadraticFormUp,
          quadraticFormToEventFlow x = quadraticFormToEventFlow y → x = y) ∧
          quadraticFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨QuadraticFormTasteGate_single_carrier_alignment_decode_encode,
      QuadraticFormTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        QuadraticFormTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.QuadraticFormUp
