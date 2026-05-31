import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICResidualSubstitutionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICResidualSubstitutionBoundaryUp : Type where
  | mk (R S A J N F L H C P K : BHist) : MetaCICResidualSubstitutionBoundaryUp
  deriving DecidableEq

def metaCICResidualSubstitutionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICResidualSubstitutionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICResidualSubstitutionBoundaryEncodeBHist h

def metaCICResidualSubstitutionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICResidualSubstitutionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICResidualSubstitutionBoundaryDecodeBHist tail)

private theorem MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metaCICResidualSubstitutionBoundaryDecodeBHist
          (metaCICResidualSubstitutionBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICResidualSubstitutionBoundaryFields :
    MetaCICResidualSubstitutionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICResidualSubstitutionBoundaryUp.mk R S A J N F L H C P K =>
      [R, S, A, J, N, F, L, H, C, P, K]

def metaCICResidualSubstitutionBoundaryToEventFlow :
    MetaCICResidualSubstitutionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metaCICResidualSubstitutionBoundaryFields x).map
        metaCICResidualSubstitutionBoundaryEncodeBHist

private def metaCICResidualSubstitutionBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICResidualSubstitutionBoundaryEventAt index rest

def metaCICResidualSubstitutionBoundaryFromEventFlow (ef : EventFlow) :
    Option MetaCICResidualSubstitutionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICResidualSubstitutionBoundaryUp.mk
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 0 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 1 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 2 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 3 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 4 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 5 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 6 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 7 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 8 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 9 ef))
      (metaCICResidualSubstitutionBoundaryDecodeBHist
        (metaCICResidualSubstitutionBoundaryEventAt 10 ef)))

private theorem MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICResidualSubstitutionBoundaryUp) :
    metaCICResidualSubstitutionBoundaryFromEventFlow
        (metaCICResidualSubstitutionBoundaryToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R S A J N F L H C P K =>
      change
        some
          (MetaCICResidualSubstitutionBoundaryUp.mk
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist R))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist S))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist A))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist J))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist N))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist F))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist L))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist H))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist C))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist P))
            (metaCICResidualSubstitutionBoundaryDecodeBHist
              (metaCICResidualSubstitutionBoundaryEncodeBHist K))) =
          some (MetaCICResidualSubstitutionBoundaryUp.mk R S A J N F L H C P K)
      rw [MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode A,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode J,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode N,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode F,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode L,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode K]

private theorem MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICResidualSubstitutionBoundaryUp} :
    metaCICResidualSubstitutionBoundaryToEventFlow x =
        metaCICResidualSubstitutionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICResidualSubstitutionBoundaryFromEventFlow
          (metaCICResidualSubstitutionBoundaryToEventFlow x) =
        metaCICResidualSubstitutionBoundaryFromEventFlow
          (metaCICResidualSubstitutionBoundaryToEventFlow y) :=
    congrArg metaCICResidualSubstitutionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetaCICResidualSubstitutionBoundaryUp,
      metaCICResidualSubstitutionBoundaryFields x =
          metaCICResidualSubstitutionBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ S₁ A₁ J₁ N₁ F₁ L₁ H₁ C₁ P₁ K₁ =>
      cases y with
      | mk R₂ S₂ A₂ J₂ N₂ F₂ L₂ H₂ C₂ P₂ K₂ =>
          cases hfields
          rfl

instance metaCICResidualSubstitutionBoundaryBHistCarrier :
    BHistCarrier MetaCICResidualSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICResidualSubstitutionBoundaryToEventFlow
  fromEventFlow := metaCICResidualSubstitutionBoundaryFromEventFlow

instance metaCICResidualSubstitutionBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICResidualSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICResidualSubstitutionBoundaryFromEventFlow
          (metaCICResidualSubstitutionBoundaryToEventFlow x) =
        some x
    exact MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance metaCICResidualSubstitutionBoundaryFieldFaithful :
    FieldFaithful MetaCICResidualSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICResidualSubstitutionBoundaryFields
  field_faithful :=
    MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_fields_faithful

instance metaCICResidualSubstitutionBoundaryNontrivial :
    Nontrivial MetaCICResidualSubstitutionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICResidualSubstitutionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICResidualSubstitutionBoundaryUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICResidualSubstitutionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICResidualSubstitutionBoundaryChapterTasteGate

theorem MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICResidualSubstitutionBoundaryDecodeBHist
          (metaCICResidualSubstitutionBoundaryEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICResidualSubstitutionBoundaryUp,
        metaCICResidualSubstitutionBoundaryFromEventFlow
            (metaCICResidualSubstitutionBoundaryToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICResidualSubstitutionBoundaryUp,
          metaCICResidualSubstitutionBoundaryToEventFlow x =
              metaCICResidualSubstitutionBoundaryToEventFlow y →
            x = y) ∧
          metaCICResidualSubstitutionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_decode_encode,
      MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICResidualSubstitutionBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.MetaCICResidualSubstitutionBoundaryUp
