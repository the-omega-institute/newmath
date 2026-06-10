import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CosetSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CosetSpaceUp : Type where
  | mk (G S r o H C P N : BHist) : CosetSpaceUp
  deriving DecidableEq

def cosetSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cosetSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cosetSpaceEncodeBHist h

def cosetSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cosetSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cosetSpaceDecodeBHist tail)

private theorem CosetSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cosetSpaceDecodeBHist (cosetSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cosetSpaceFields : CosetSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CosetSpaceUp.mk G S r o H C P N => [G, S, r, o, H, C, P, N]

def cosetSpaceToEventFlow : CosetSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cosetSpaceFields x).map cosetSpaceEncodeBHist

private def CosetSpaceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CosetSpaceTasteGate_single_carrier_alignment_eventAt index rest

def cosetSpaceFromEventFlow (ef : EventFlow) : Option CosetSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CosetSpaceUp.mk
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cosetSpaceDecodeBHist (CosetSpaceTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem CosetSpaceTasteGate_single_carrier_alignment_round_trip
    (x : CosetSpaceUp) :
    cosetSpaceFromEventFlow (cosetSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G S r o H C P N =>
      change
        some
          (CosetSpaceUp.mk
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist G))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist S))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist r))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist o))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist H))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist C))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist P))
            (cosetSpaceDecodeBHist (cosetSpaceEncodeBHist N))) =
          some (CosetSpaceUp.mk G S r o H C P N)
      rw [CosetSpaceTasteGate_single_carrier_alignment_decode_encode G,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode S,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode r,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode o,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode H,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode C,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode P,
        CosetSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CosetSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CosetSpaceUp} :
    cosetSpaceToEventFlow x = cosetSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cosetSpaceFromEventFlow (cosetSpaceToEventFlow x) =
        cosetSpaceFromEventFlow (cosetSpaceToEventFlow y) :=
    congrArg cosetSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CosetSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CosetSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CosetSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CosetSpaceUp, cosetSpaceFields x = cosetSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ S₁ r₁ o₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ S₂ r₂ o₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cosetSpaceBHistCarrier : BHistCarrier CosetSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cosetSpaceToEventFlow
  fromEventFlow := cosetSpaceFromEventFlow

instance cosetSpaceChapterTasteGate : ChapterTasteGate CosetSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cosetSpaceFromEventFlow (cosetSpaceToEventFlow x) = some x
    exact CosetSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CosetSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cosetSpaceFieldFaithful : FieldFaithful CosetSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cosetSpaceFields
  field_faithful := CosetSpaceTasteGate_single_carrier_alignment_fields_faithful

instance cosetSpaceNontrivial : BEDC.Meta.TasteGate.Nontrivial CosetSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CosetSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CosetSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CosetSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cosetSpaceChapterTasteGate

theorem CosetSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CosetSpaceUp) ∧
      Nonempty (FieldFaithful CosetSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CosetSpaceUp) ∧
          (∀ h : BHist, cosetSpaceDecodeBHist (cosetSpaceEncodeBHist h) = h) ∧
            (∀ x : CosetSpaceUp, cosetSpaceFromEventFlow (cosetSpaceToEventFlow x) = some x) ∧
              (∀ x y : CosetSpaceUp,
                cosetSpaceToEventFlow x = cosetSpaceToEventFlow y → x = y) ∧
                cosetSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨cosetSpaceChapterTasteGate⟩,
      ⟨cosetSpaceFieldFaithful⟩,
      ⟨cosetSpaceNontrivial⟩,
      CosetSpaceTasteGate_single_carrier_alignment_decode_encode,
      CosetSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CosetSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CosetSpaceUp
