import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessSpaceUp : Type where
  | mk (X L G T C0 C1 H C P N : BHist) : ApartnessSpaceUp
  deriving DecidableEq

def apartnessSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessSpaceEncodeBHist h

def apartnessSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessSpaceDecodeBHist tail)

private theorem apartnessSpace_decode_encode_bhist :
    ∀ h : BHist, apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apartnessSpaceFields : ApartnessSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessSpaceUp.mk X L G T C0 C1 H C P N => [X, L, G, T, C0, C1, H, C, P, N]

def apartnessSpaceToEventFlow : ApartnessSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessSpaceUp.mk X L G T C0 C1 H C P N =>
      [apartnessSpaceEncodeBHist X,
        apartnessSpaceEncodeBHist L,
        apartnessSpaceEncodeBHist G,
        apartnessSpaceEncodeBHist T,
        apartnessSpaceEncodeBHist C0,
        apartnessSpaceEncodeBHist C1,
        apartnessSpaceEncodeBHist H,
        apartnessSpaceEncodeBHist C,
        apartnessSpaceEncodeBHist P,
        apartnessSpaceEncodeBHist N]

private def apartnessSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => apartnessSpaceEventAtDefault index rest

def apartnessSpaceFromEventFlow (ef : EventFlow) : Option ApartnessSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ApartnessSpaceUp.mk
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 0 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 1 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 2 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 3 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 4 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 5 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 6 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 7 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 8 ef))
      (apartnessSpaceDecodeBHist (apartnessSpaceEventAtDefault 9 ef)))

private theorem apartnessSpace_round_trip :
    ∀ x : ApartnessSpaceUp,
      apartnessSpaceFromEventFlow (apartnessSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X L G T C0 C1 H C P N =>
      change
        some
          (ApartnessSpaceUp.mk
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist X))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist L))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist G))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist T))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist C0))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist C1))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist H))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist C))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist P))
            (apartnessSpaceDecodeBHist (apartnessSpaceEncodeBHist N))) =
          some (ApartnessSpaceUp.mk X L G T C0 C1 H C P N)
      rw [apartnessSpace_decode_encode_bhist X,
        apartnessSpace_decode_encode_bhist L,
        apartnessSpace_decode_encode_bhist G,
        apartnessSpace_decode_encode_bhist T,
        apartnessSpace_decode_encode_bhist C0,
        apartnessSpace_decode_encode_bhist C1,
        apartnessSpace_decode_encode_bhist H,
        apartnessSpace_decode_encode_bhist C,
        apartnessSpace_decode_encode_bhist P,
        apartnessSpace_decode_encode_bhist N]

private theorem apartnessSpaceToEventFlow_injective {x y : ApartnessSpaceUp} :
    apartnessSpaceToEventFlow x = apartnessSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessSpaceFromEventFlow (apartnessSpaceToEventFlow x) =
        apartnessSpaceFromEventFlow (apartnessSpaceToEventFlow y) :=
    congrArg apartnessSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apartnessSpace_round_trip x).symm
      (Eq.trans hread (apartnessSpace_round_trip y)))

private theorem apartnessSpace_field_faithful :
    ∀ x y : ApartnessSpaceUp, apartnessSpaceFields x = apartnessSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ L₁ G₁ T₁ C0₁ C1₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ L₂ G₂ T₂ C0₂ C1₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance apartnessSpaceBHistCarrier : BHistCarrier ApartnessSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessSpaceToEventFlow
  fromEventFlow := apartnessSpaceFromEventFlow

instance apartnessSpaceChapterTasteGate : ChapterTasteGate ApartnessSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apartnessSpaceFromEventFlow (apartnessSpaceToEventFlow x) = some x
    exact apartnessSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apartnessSpaceToEventFlow_injective heq)

instance apartnessSpaceFieldFaithful : FieldFaithful ApartnessSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apartnessSpaceFields
  field_faithful := apartnessSpace_field_faithful

instance apartnessSpaceNontrivial : Nontrivial ApartnessSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApartnessSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApartnessSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApartnessSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apartnessSpaceChapterTasteGate

theorem ApartnessSpaceTasteGate_single_carrier_alignment :
    let base :=
      ApartnessSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    let shifted :=
      ApartnessSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    Nonempty (Nontrivial ApartnessSpaceUp) ∧
      Nonempty (ChapterTasteGate ApartnessSpaceUp) ∧
        Nonempty (FieldFaithful ApartnessSpaceUp) ∧
          apartnessSpaceFields base ≠ apartnessSpaceFields shifted ∧
            apartnessSpaceToEventFlow base ≠ apartnessSpaceToEventFlow shifted := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨apartnessSpaceNontrivial⟩
  · constructor
    · exact ⟨apartnessSpaceChapterTasteGate⟩
    · constructor
      · exact ⟨apartnessSpaceFieldFaithful⟩
      · constructor
        · intro h
          cases h
        · intro h
          exact
            (apartnessSpaceNontrivial.witness_pair.2.2
              (apartnessSpaceToEventFlow_injective h))

end BEDC.Derived.ApartnessSpaceUp
