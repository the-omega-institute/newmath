import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetrizableCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetrizableCompletionUp : Type where
  | mk (T M Q K S R E H C P N : BHist) : MetrizableCompletionUp
  deriving DecidableEq

def metrizableCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metrizableCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metrizableCompletionEncodeBHist h

def metrizableCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metrizableCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metrizableCompletionDecodeBHist tail)

private theorem MetrizableCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metrizableCompletionFields : MetrizableCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetrizableCompletionUp.mk T M Q K S R E H C P N => [T, M, Q, K, S, R, E, H, C, P, N]

def metrizableCompletionToEventFlow : MetrizableCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetrizableCompletionUp.mk T M Q K S R E H C P N =>
      [metrizableCompletionEncodeBHist T,
        metrizableCompletionEncodeBHist M,
        metrizableCompletionEncodeBHist Q,
        metrizableCompletionEncodeBHist K,
        metrizableCompletionEncodeBHist S,
        metrizableCompletionEncodeBHist R,
        metrizableCompletionEncodeBHist E,
        metrizableCompletionEncodeBHist H,
        metrizableCompletionEncodeBHist C,
        metrizableCompletionEncodeBHist P,
        metrizableCompletionEncodeBHist N]

private def metrizableCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metrizableCompletionEventAt index rest

def metrizableCompletionFromEventFlow : EventFlow → Option MetrizableCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MetrizableCompletionUp.mk
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 0 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 1 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 2 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 3 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 4 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 5 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 6 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 7 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 8 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 9 ef))
          (metrizableCompletionDecodeBHist (metrizableCompletionEventAt 10 ef)))

private theorem MetrizableCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetrizableCompletionUp,
      metrizableCompletionFromEventFlow (metrizableCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M Q K S R E H C P N =>
      change
        some
          (MetrizableCompletionUp.mk
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist T))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist M))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist Q))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist K))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist S))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist R))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist E))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist H))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist C))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist P))
            (metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist N))) =
          some (MetrizableCompletionUp.mk T M Q K S R E H C P N)
      rw [MetrizableCompletionTasteGate_single_carrier_alignment_decode T,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode M,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode Q,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode K,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode S,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode R,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode E,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode H,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode C,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode P,
        MetrizableCompletionTasteGate_single_carrier_alignment_decode N]

private theorem MetrizableCompletionTasteGate_single_carrier_alignment_injective
    {x y : MetrizableCompletionUp} :
    metrizableCompletionToEventFlow x = metrizableCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metrizableCompletionFromEventFlow (metrizableCompletionToEventFlow x) =
        metrizableCompletionFromEventFlow (metrizableCompletionToEventFlow y) :=
    congrArg metrizableCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetrizableCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetrizableCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetrizableCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetrizableCompletionUp,
      metrizableCompletionFields x = metrizableCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ M₁ Q₁ K₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ M₂ Q₂ K₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metrizableCompletionBHistCarrier : BHistCarrier MetrizableCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metrizableCompletionToEventFlow
  fromEventFlow := metrizableCompletionFromEventFlow

instance metrizableCompletionChapterTasteGate : ChapterTasteGate MetrizableCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metrizableCompletionFromEventFlow (metrizableCompletionToEventFlow x) = some x
    exact MetrizableCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetrizableCompletionTasteGate_single_carrier_alignment_injective heq)

instance metrizableCompletionFieldFaithful : FieldFaithful MetrizableCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metrizableCompletionFields
  field_faithful := MetrizableCompletionTasteGate_single_carrier_alignment_fields

instance metrizableCompletionNontrivial : Nontrivial MetrizableCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetrizableCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetrizableCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetrizableCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetrizableCompletionUp) ∧
      Nonempty (FieldFaithful MetrizableCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetrizableCompletionUp) ∧
          (∀ h : BHist, metrizableCompletionDecodeBHist (metrizableCompletionEncodeBHist h) = h) ∧
            (∀ x : MetrizableCompletionUp,
              metrizableCompletionFromEventFlow (metrizableCompletionToEventFlow x) = some x) ∧
              (∀ x y : MetrizableCompletionUp,
                metrizableCompletionToEventFlow x = metrizableCompletionToEventFlow y → x = y) ∧
                metrizableCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨metrizableCompletionChapterTasteGate⟩,
      ⟨metrizableCompletionFieldFaithful⟩,
      ⟨metrizableCompletionNontrivial⟩,
      MetrizableCompletionTasteGate_single_carrier_alignment_decode,
      MetrizableCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MetrizableCompletionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.MetrizableCompletionUp
