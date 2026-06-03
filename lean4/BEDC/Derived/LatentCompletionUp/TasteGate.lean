import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LatentCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LatentCompletionUp : Type where
  | mk (O E L D M K H C P N : BHist) : LatentCompletionUp
  deriving DecidableEq

def latentCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: latentCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: latentCompletionEncodeBHist h

def latentCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (latentCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (latentCompletionDecodeBHist tail)

private theorem LatentCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      latentCompletionDecodeBHist (latentCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def latentCompletionFields : LatentCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LatentCompletionUp.mk O E L D M K H C P N => [O, E, L, D, M, K, H, C, P, N]

def latentCompletionToEventFlow : LatentCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (latentCompletionFields x).map latentCompletionEncodeBHist

private def LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault index rest

def latentCompletionFromEventFlow (ef : EventFlow) : Option LatentCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LatentCompletionUp.mk
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (latentCompletionDecodeBHist
        (LatentCompletionTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem LatentCompletionTasteGate_single_carrier_alignment_round_trip
    (x : LatentCompletionUp) :
    latentCompletionFromEventFlow (latentCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O E L D M K H C P N =>
      change
        some
          (LatentCompletionUp.mk
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist O))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist E))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist L))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist D))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist M))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist K))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist H))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist C))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist P))
            (latentCompletionDecodeBHist (latentCompletionEncodeBHist N))) =
          some (LatentCompletionUp.mk O E L D M K H C P N)
      rw [LatentCompletionTasteGate_single_carrier_alignment_decode_encode O,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode E,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode L,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode D,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode M,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode K,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode H,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode C,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode P,
        LatentCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LatentCompletionTasteGate_single_carrier_alignment_injective
    {x y : LatentCompletionUp} :
    latentCompletionToEventFlow x = latentCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      latentCompletionFromEventFlow (latentCompletionToEventFlow x) =
        latentCompletionFromEventFlow (latentCompletionToEventFlow y) :=
    congrArg latentCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LatentCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LatentCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LatentCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : LatentCompletionUp,
      latentCompletionFields x = latentCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ E₁ L₁ D₁ M₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ E₂ L₂ D₂ M₂ K₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance latentCompletionBHistCarrier : BHistCarrier LatentCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := latentCompletionToEventFlow
  fromEventFlow := latentCompletionFromEventFlow

instance latentCompletionChapterTasteGate :
    ChapterTasteGate LatentCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change latentCompletionFromEventFlow (latentCompletionToEventFlow x) = some x
    exact LatentCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LatentCompletionTasteGate_single_carrier_alignment_injective heq)

instance latentCompletionFieldFaithful : FieldFaithful LatentCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := latentCompletionFields
  field_faithful := LatentCompletionTasteGate_single_carrier_alignment_fields

instance latentCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LatentCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LatentCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LatentCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def LatentCompletionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LatentCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  latentCompletionChapterTasteGate

theorem LatentCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, latentCompletionDecodeBHist (latentCompletionEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate LatentCompletionUp) ∧
        Nonempty (FieldFaithful LatentCompletionUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial LatentCompletionUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LatentCompletionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨latentCompletionChapterTasteGate⟩
    · constructor
      · exact ⟨latentCompletionFieldFaithful⟩
      · exact ⟨latentCompletionNontrivial⟩

end BEDC.Derived.LatentCompletionUp
