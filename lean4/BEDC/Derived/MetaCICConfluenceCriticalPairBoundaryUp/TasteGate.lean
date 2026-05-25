import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceCriticalPairBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceCriticalPairBoundaryUp : Type where
  | mk (R K J E D S U H C P N : BHist) : MetaCICConfluenceCriticalPairBoundaryUp
  deriving DecidableEq

def metaCICConfluenceCriticalPairBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceCriticalPairBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceCriticalPairBoundaryEncodeBHist h

def metaCICConfluenceCriticalPairBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceCriticalPairBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceCriticalPairBoundaryDecodeBHist tail)

private theorem MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metaCICConfluenceCriticalPairBoundaryDecodeBHist
          (metaCICConfluenceCriticalPairBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICConfluenceCriticalPairBoundaryFields :
    MetaCICConfluenceCriticalPairBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceCriticalPairBoundaryUp.mk R K J E D S U H C P N =>
      [R, K, J, E, D, S, U, H, C, P, N]

def metaCICConfluenceCriticalPairBoundaryToEventFlow :
    MetaCICConfluenceCriticalPairBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metaCICConfluenceCriticalPairBoundaryFields x).map
        metaCICConfluenceCriticalPairBoundaryEncodeBHist

private def metaCICConfluenceCriticalPairBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICConfluenceCriticalPairBoundaryEventAt index rest

def metaCICConfluenceCriticalPairBoundaryFromEventFlow (ef : EventFlow) :
    Option MetaCICConfluenceCriticalPairBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICConfluenceCriticalPairBoundaryUp.mk
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 0 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 1 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 2 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 3 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 4 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 5 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 6 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 7 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 8 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 9 ef))
      (metaCICConfluenceCriticalPairBoundaryDecodeBHist
        (metaCICConfluenceCriticalPairBoundaryEventAt 10 ef)))

private theorem MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICConfluenceCriticalPairBoundaryUp) :
    metaCICConfluenceCriticalPairBoundaryFromEventFlow
        (metaCICConfluenceCriticalPairBoundaryToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R K J E D S U H C P N =>
      change
        some
          (MetaCICConfluenceCriticalPairBoundaryUp.mk
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist R))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist K))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist J))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist E))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist D))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist S))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist U))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist H))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist C))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist P))
            (metaCICConfluenceCriticalPairBoundaryDecodeBHist
              (metaCICConfluenceCriticalPairBoundaryEncodeBHist N))) =
          some (MetaCICConfluenceCriticalPairBoundaryUp.mk R K J E D S U H C P N)
      rw [MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode K,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode J,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode E,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode D,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode U,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICConfluenceCriticalPairBoundaryUp} :
    metaCICConfluenceCriticalPairBoundaryToEventFlow x =
        metaCICConfluenceCriticalPairBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceCriticalPairBoundaryFromEventFlow
          (metaCICConfluenceCriticalPairBoundaryToEventFlow x) =
        metaCICConfluenceCriticalPairBoundaryFromEventFlow
          (metaCICConfluenceCriticalPairBoundaryToEventFlow y) :=
    congrArg metaCICConfluenceCriticalPairBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetaCICConfluenceCriticalPairBoundaryUp,
      metaCICConfluenceCriticalPairBoundaryFields x =
          metaCICConfluenceCriticalPairBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ K₁ J₁ E₁ D₁ S₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ K₂ J₂ E₂ D₂ S₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metaCICConfluenceCriticalPairBoundaryBHistCarrier :
    BHistCarrier MetaCICConfluenceCriticalPairBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceCriticalPairBoundaryToEventFlow
  fromEventFlow := metaCICConfluenceCriticalPairBoundaryFromEventFlow

instance metaCICConfluenceCriticalPairBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceCriticalPairBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConfluenceCriticalPairBoundaryFromEventFlow
          (metaCICConfluenceCriticalPairBoundaryToEventFlow x) =
        some x
    exact MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance metaCICConfluenceCriticalPairBoundaryFieldFaithful :
    FieldFaithful MetaCICConfluenceCriticalPairBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICConfluenceCriticalPairBoundaryFields
  field_faithful :=
    MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_fields_faithful

instance metaCICConfluenceCriticalPairBoundaryNontrivial :
    Nontrivial MetaCICConfluenceCriticalPairBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICConfluenceCriticalPairBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICConfluenceCriticalPairBoundaryUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICConfluenceCriticalPairBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceCriticalPairBoundaryChapterTasteGate

theorem MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICConfluenceCriticalPairBoundaryDecodeBHist
          (metaCICConfluenceCriticalPairBoundaryEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICConfluenceCriticalPairBoundaryUp,
        metaCICConfluenceCriticalPairBoundaryFromEventFlow
            (metaCICConfluenceCriticalPairBoundaryToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICConfluenceCriticalPairBoundaryUp,
          metaCICConfluenceCriticalPairBoundaryToEventFlow x =
              metaCICConfluenceCriticalPairBoundaryToEventFlow y →
            x = y) ∧
          metaCICConfluenceCriticalPairBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_decode_encode,
      MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICConfluenceCriticalPairBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.MetaCICConfluenceCriticalPairBoundaryUp
