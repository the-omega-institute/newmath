import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalEndpointBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalEndpointBudgetUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (T K B F O H C P N G : BHist) : MetaCICNormalEndpointBudgetUp
  deriving DecidableEq

def metaCICNormalEndpointBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalEndpointBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalEndpointBudgetEncodeBHist h

def metaCICNormalEndpointBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICNormalEndpointBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICNormalEndpointBudgetDecodeBHist tail)

private theorem MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metaCICNormalEndpointBudgetDecodeBHist
          (metaCICNormalEndpointBudgetEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICNormalEndpointBudgetFields :
    MetaCICNormalEndpointBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalEndpointBudgetUp.mk T K B F O H C P N G =>
      [T, K, B, F, O, H, C, P, N, G]

def metaCICNormalEndpointBudgetToEventFlow :
    MetaCICNormalEndpointBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metaCICNormalEndpointBudgetFields x).map metaCICNormalEndpointBudgetEncodeBHist

private def metaCICNormalEndpointBudgetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICNormalEndpointBudgetEventAt index rest

def metaCICNormalEndpointBudgetFromEventFlow :
    EventFlow → Option MetaCICNormalEndpointBudgetUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICNormalEndpointBudgetUp.mk
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 0 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 1 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 2 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 3 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 4 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 5 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 6 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 7 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 8 ef))
      (metaCICNormalEndpointBudgetDecodeBHist (metaCICNormalEndpointBudgetEventAt 9 ef)))

private theorem MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICNormalEndpointBudgetUp) :
    metaCICNormalEndpointBudgetFromEventFlow
        (metaCICNormalEndpointBudgetToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T K B F O H C P N G =>
      change
        some
          (MetaCICNormalEndpointBudgetUp.mk
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist T))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist K))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist B))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist F))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist O))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist H))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist C))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist P))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist N))
            (metaCICNormalEndpointBudgetDecodeBHist
              (metaCICNormalEndpointBudgetEncodeBHist G))) =
          some (MetaCICNormalEndpointBudgetUp.mk T K B F O H C P N G)
      rw [MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode T,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode K,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode B,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode F,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode O,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode H,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode C,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode P,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode N,
        MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode G]

private theorem MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_injective
    {x y : MetaCICNormalEndpointBudgetUp} :
    metaCICNormalEndpointBudgetToEventFlow x =
      metaCICNormalEndpointBudgetToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICNormalEndpointBudgetFromEventFlow
          (metaCICNormalEndpointBudgetToEventFlow x) =
        metaCICNormalEndpointBudgetFromEventFlow
          (metaCICNormalEndpointBudgetToEventFlow y) :=
    congrArg metaCICNormalEndpointBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MetaCICNormalEndpointBudgetUp,
      metaCICNormalEndpointBudgetFields x = metaCICNormalEndpointBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ K₁ B₁ F₁ O₁ H₁ C₁ P₁ N₁ G₁ =>
      cases y with
      | mk T₂ K₂ B₂ F₂ O₂ H₂ C₂ P₂ N₂ G₂ =>
          cases hfields
          rfl

instance metaCICNormalEndpointBudgetBHistCarrier :
    BHistCarrier MetaCICNormalEndpointBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalEndpointBudgetToEventFlow
  fromEventFlow := metaCICNormalEndpointBudgetFromEventFlow

instance metaCICNormalEndpointBudgetChapterTasteGate :
    ChapterTasteGate MetaCICNormalEndpointBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalEndpointBudgetFromEventFlow
          (metaCICNormalEndpointBudgetToEventFlow x) =
        some x
    exact MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_injective heq)

instance metaCICNormalEndpointBudgetFieldFaithful :
    FieldFaithful MetaCICNormalEndpointBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICNormalEndpointBudgetFields
  field_faithful :=
    MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_fields_faithful

instance metaCICNormalEndpointBudgetNontrivial :
    Nontrivial MetaCICNormalEndpointBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalEndpointBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICNormalEndpointBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICNormalEndpointBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICNormalEndpointBudgetChapterTasteGate

theorem MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalEndpointBudgetDecodeBHist
          (metaCICNormalEndpointBudgetEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICNormalEndpointBudgetUp,
        metaCICNormalEndpointBudgetFromEventFlow
            (metaCICNormalEndpointBudgetToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICNormalEndpointBudgetUp,
          metaCICNormalEndpointBudgetToEventFlow x =
            metaCICNormalEndpointBudgetToEventFlow y →
              x = y) ∧
          metaCICNormalEndpointBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_decode_encode,
      MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_round_trip,
      fun x y => MetaCICNormalEndpointBudgetTasteGate_single_carrier_alignment_injective,
      rfl⟩

end BEDC.Derived.MetaCICNormalEndpointBudgetUp
