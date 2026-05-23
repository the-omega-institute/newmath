import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyPrecompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyPrecompletionUp : Type where
  | mk (W R D S E H C P N : BHist) : CauchyPrecompletionUp
  deriving DecidableEq

def cauchyPrecompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyPrecompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyPrecompletionEncodeBHist h

def cauchyPrecompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyPrecompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyPrecompletionDecodeBHist tail)

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyPrecompletionFields : CauchyPrecompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyPrecompletionUp.mk W R D S E H C P N => [W, R, D, S, E, H, C, P, N]

def cauchyPrecompletionToEventFlow : CauchyPrecompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyPrecompletionFields x).map cauchyPrecompletionEncodeBHist

private def cauchyPrecompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyPrecompletionEventAt index rest

def cauchyPrecompletionFromEventFlow (ef : EventFlow) : Option CauchyPrecompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyPrecompletionUp.mk
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 0 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 1 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 2 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 3 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 4 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 5 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 6 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 7 ef))
      (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEventAt 8 ef)))

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip
    (x : CauchyPrecompletionUp) :
    cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W R D S E H C P N =>
      change
        some
          (CauchyPrecompletionUp.mk
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist W))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist R))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist D))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist S))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist E))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist H))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist C))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist P))
            (cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist N))) =
          some (CauchyPrecompletionUp.mk W R D S E H C P N)
      rw [CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode W,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyPrecompletionUp} :
    cauchyPrecompletionToEventFlow x = cauchyPrecompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) =
        cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow y) :=
    congrArg cauchyPrecompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyPrecompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyPrecompletionUp, cauchyPrecompletionFields x = cauchyPrecompletionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ R₁ D₁ S₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ R₂ D₂ S₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyPrecompletionBHistCarrier : BHistCarrier CauchyPrecompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyPrecompletionToEventFlow
  fromEventFlow := cauchyPrecompletionFromEventFlow

instance cauchyPrecompletionChapterTasteGate : ChapterTasteGate CauchyPrecompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) = some x
    exact CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyPrecompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyPrecompletionFieldFaithful : FieldFaithful CauchyPrecompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyPrecompletionFields
  field_faithful := CauchyPrecompletionTasteGate_single_carrier_alignment_fields_faithful

instance cauchyPrecompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyPrecompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyPrecompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyPrecompletionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyPrecompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyPrecompletionChapterTasteGate

theorem CauchyPrecompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyPrecompletionUp) ∧
      Nonempty (FieldFaithful CauchyPrecompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyPrecompletionUp) ∧
          (∀ h : BHist, cauchyPrecompletionDecodeBHist (cauchyPrecompletionEncodeBHist h) = h) ∧
            (∀ x : CauchyPrecompletionUp,
              cauchyPrecompletionFromEventFlow (cauchyPrecompletionToEventFlow x) = some x) ∧
              (∀ x y : CauchyPrecompletionUp,
                cauchyPrecompletionToEventFlow x = cauchyPrecompletionToEventFlow y → x = y) ∧
                cauchyPrecompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyPrecompletionChapterTasteGate⟩,
      ⟨cauchyPrecompletionFieldFaithful⟩,
      ⟨cauchyPrecompletionNontrivial⟩,
      CauchyPrecompletionTasteGate_single_carrier_alignment_decode_encode,
      CauchyPrecompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyPrecompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyPrecompletionUp.TasteGate
