import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FirstCountableSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FirstCountableSpaceUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (X T M L D S R H C P N : BHist) : FirstCountableSpaceUp
  deriving DecidableEq

def firstCountableSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: firstCountableSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: firstCountableSpaceEncodeBHist h

def firstCountableSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (firstCountableSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (firstCountableSpaceDecodeBHist tail)

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def firstCountableSpaceFields : FirstCountableSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FirstCountableSpaceUp.mk X T M L D S R H C P N => [X, T, M, L, D, S, R, H, C, P, N]

def firstCountableSpaceToEventFlow : FirstCountableSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (firstCountableSpaceFields x).map firstCountableSpaceEncodeBHist

private def firstCountableSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => firstCountableSpaceEventAt index rest

def firstCountableSpaceFromEventFlow (ef : EventFlow) : Option FirstCountableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FirstCountableSpaceUp.mk
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 0 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 1 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 2 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 3 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 4 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 5 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 6 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 7 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 8 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 9 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAt 10 ef)))

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip
    (x : FirstCountableSpaceUp) :
    firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X T M L D S R H C P N =>
      change
        some
          (FirstCountableSpaceUp.mk
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist X))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist T))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist M))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist L))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist D))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist S))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist R))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist H))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist C))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist P))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist N))) =
          some (FirstCountableSpaceUp.mk X T M L D S R H C P N)
      rw [FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode X,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode T,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode M,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode L,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode D,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode S,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode R,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode H,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode C,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode P,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FirstCountableSpaceUp} :
    firstCountableSpaceToEventFlow x = firstCountableSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) =
        firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow y) :=
    congrArg firstCountableSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FirstCountableSpaceUp,
      firstCountableSpaceFields x = firstCountableSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ T₁ M₁ L₁ D₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ T₂ M₂ L₂ D₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance firstCountableSpaceBHistCarrier : BHistCarrier FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := firstCountableSpaceToEventFlow
  fromEventFlow := firstCountableSpaceFromEventFlow

instance firstCountableSpaceChapterTasteGate :
    ChapterTasteGate FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) = some x
    exact FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FirstCountableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance firstCountableSpaceFieldFaithful : FieldFaithful FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := firstCountableSpaceFields
  field_faithful := FirstCountableSpaceTasteGate_single_carrier_alignment_fields_faithful

instance firstCountableSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FirstCountableSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FirstCountableSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FirstCountableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  firstCountableSpaceChapterTasteGate

theorem FirstCountableSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FirstCountableSpaceUp) ∧
      Nonempty (FieldFaithful FirstCountableSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FirstCountableSpaceUp) ∧
          (∀ h : BHist,
            firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist h) = h) ∧
            (∀ x : FirstCountableSpaceUp,
              firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) = some x) ∧
              (∀ x y : FirstCountableSpaceUp,
                firstCountableSpaceToEventFlow x = firstCountableSpaceToEventFlow y → x = y) ∧
                firstCountableSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨firstCountableSpaceChapterTasteGate⟩,
      ⟨firstCountableSpaceFieldFaithful⟩,
      ⟨firstCountableSpaceNontrivial⟩,
      FirstCountableSpaceTasteGate_single_carrier_alignment_decode_encode,
      FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FirstCountableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FirstCountableSpaceUp.TasteGate
