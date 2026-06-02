import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICFrontierCriticalPairUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICFrontierCriticalPairUp : Type where
  | mk (R F J E U S H C P N : BHist) : MetaCICFrontierCriticalPairUp
  deriving DecidableEq

def metaCICFrontierCriticalPairEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICFrontierCriticalPairEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICFrontierCriticalPairEncodeBHist h

def metaCICFrontierCriticalPairDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICFrontierCriticalPairDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICFrontierCriticalPairDecodeBHist tail)

private def MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest =>
      MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt n rest

private theorem MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metaCICFrontierCriticalPairDecodeBHist
          (metaCICFrontierCriticalPairEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICFrontierCriticalPairFields :
    MetaCICFrontierCriticalPairUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICFrontierCriticalPairUp.mk R F J E U S H C P N =>
      [R, F, J, E, U, S, H, C, P, N]

def metaCICFrontierCriticalPairToEventFlow :
    MetaCICFrontierCriticalPairUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICFrontierCriticalPairUp.mk R F J E U S H C P N =>
      [metaCICFrontierCriticalPairEncodeBHist R,
        metaCICFrontierCriticalPairEncodeBHist F,
        metaCICFrontierCriticalPairEncodeBHist J,
        metaCICFrontierCriticalPairEncodeBHist E,
        metaCICFrontierCriticalPairEncodeBHist U,
        metaCICFrontierCriticalPairEncodeBHist S,
        metaCICFrontierCriticalPairEncodeBHist H,
        metaCICFrontierCriticalPairEncodeBHist C,
        metaCICFrontierCriticalPairEncodeBHist P,
        metaCICFrontierCriticalPairEncodeBHist N]

def metaCICFrontierCriticalPairFromEventFlow :
    EventFlow → Option MetaCICFrontierCriticalPairUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MetaCICFrontierCriticalPairUp.mk
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 0 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 1 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 2 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 3 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 4 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 5 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 6 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 7 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 8 ef))
          (metaCICFrontierCriticalPairDecodeBHist
            (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_rawAt 9 ef)))

private theorem MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICFrontierCriticalPairUp,
      metaCICFrontierCriticalPairFromEventFlow
          (metaCICFrontierCriticalPairToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R F J E U S H C P N =>
      change
        some
          (MetaCICFrontierCriticalPairUp.mk
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist R))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist F))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist J))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist E))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist U))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist S))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist H))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist C))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist P))
            (metaCICFrontierCriticalPairDecodeBHist
              (metaCICFrontierCriticalPairEncodeBHist N))) =
          some (MetaCICFrontierCriticalPairUp.mk R F J E U S H C P N)
      rw [MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode R,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode F,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode J,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode E,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode U,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode S,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode H,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode C,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode P,
        MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode N]

private theorem MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_injective
    {x y : MetaCICFrontierCriticalPairUp} :
    metaCICFrontierCriticalPairToEventFlow x =
        metaCICFrontierCriticalPairToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICFrontierCriticalPairFromEventFlow
          (metaCICFrontierCriticalPairToEventFlow x) =
        metaCICFrontierCriticalPairFromEventFlow
          (metaCICFrontierCriticalPairToEventFlow y) :=
    congrArg metaCICFrontierCriticalPairFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetaCICFrontierCriticalPairUp,
      metaCICFrontierCriticalPairFields x = metaCICFrontierCriticalPairFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ F₁ J₁ E₁ U₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ F₂ J₂ E₂ U₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metaCICFrontierCriticalPairBHistCarrier :
    BHistCarrier MetaCICFrontierCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICFrontierCriticalPairToEventFlow
  fromEventFlow := metaCICFrontierCriticalPairFromEventFlow

instance metaCICFrontierCriticalPairChapterTasteGate :
    ChapterTasteGate MetaCICFrontierCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICFrontierCriticalPairFromEventFlow
          (metaCICFrontierCriticalPairToEventFlow x) =
        some x
    exact MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_injective heq)

instance metaCICFrontierCriticalPairFieldFaithful :
    FieldFaithful MetaCICFrontierCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICFrontierCriticalPairFields
  field_faithful := MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_fields

instance metaCICFrontierCriticalPairNontrivial :
    Nontrivial MetaCICFrontierCriticalPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICFrontierCriticalPairUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICFrontierCriticalPairUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICFrontierCriticalPairUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICFrontierCriticalPairChapterTasteGate

theorem MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICFrontierCriticalPairDecodeBHist
          (metaCICFrontierCriticalPairEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICFrontierCriticalPairUp,
        metaCICFrontierCriticalPairFromEventFlow
            (metaCICFrontierCriticalPairToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICFrontierCriticalPairUp,
          metaCICFrontierCriticalPairToEventFlow x =
              metaCICFrontierCriticalPairToEventFlow y →
            x = y) ∧
          metaCICFrontierCriticalPairEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_decode,
      ⟨MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _x _y heq =>
            MetaCICFrontierCriticalPairTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.MetaCICFrontierCriticalPairUp
