import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleeneTreeBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleeneTreeBoundaryUp : Type where
  | mk (K F S R E O H C P N : BHist) : KleeneTreeBoundaryUp
  deriving DecidableEq

def kleeneTreeBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kleeneTreeBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kleeneTreeBoundaryEncodeBHist h

def kleeneTreeBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kleeneTreeBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kleeneTreeBoundaryDecodeBHist tail)

private theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kleeneTreeBoundaryFields : KleeneTreeBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneTreeBoundaryUp.mk K F S R E O H C P N => [K, F, S, R, E, O, H, C, P, N]

def kleeneTreeBoundaryToEventFlow : KleeneTreeBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (kleeneTreeBoundaryFields x).map kleeneTreeBoundaryEncodeBHist

private def kleeneTreeBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kleeneTreeBoundaryEventAtDefault index rest

def kleeneTreeBoundaryFromEventFlow (ef : EventFlow) : Option KleeneTreeBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KleeneTreeBoundaryUp.mk
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 0 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 1 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 2 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 3 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 4 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 5 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 6 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 7 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 8 ef))
      (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEventAtDefault 9 ef)))

private theorem kleeneTreeBoundary_round_trip :
    ∀ x : KleeneTreeBoundaryUp,
      kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F S R E O H C P N =>
      change
        some
          (KleeneTreeBoundaryUp.mk
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist K))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist F))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist S))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist R))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist E))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist O))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist H))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist C))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist P))
            (kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist N))) =
          some (KleeneTreeBoundaryUp.mk K F S R E O H C P N)
      rw [KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode K,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode F,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode E,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode O,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem kleeneTreeBoundaryToEventFlow_injective
    {x y : KleeneTreeBoundaryUp} :
    kleeneTreeBoundaryToEventFlow x = kleeneTreeBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) =
        kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow y) :=
    congrArg kleeneTreeBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kleeneTreeBoundary_round_trip x).symm
      (Eq.trans hread (kleeneTreeBoundary_round_trip y)))

private theorem kleeneTreeBoundary_field_faithful :
    ∀ x y : KleeneTreeBoundaryUp,
      kleeneTreeBoundaryFields x = kleeneTreeBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K₁ F₁ S₁ R₁ E₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ S₂ R₂ E₂ O₂ H₂ C₂ P₂ N₂ =>
          change [K₁, F₁, S₁, R₁, E₁, O₁, H₁, C₁, P₁, N₁] =
            [K₂, F₂, S₂, R₂, E₂, O₂, H₂, C₂, P₂, N₂] at h
          injection h with hK t1
          injection t1 with hF t2
          injection t2 with hS t3
          injection t3 with hR t4
          injection t4 with hE t5
          injection t5 with hO t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hK
          cases hF
          cases hS
          cases hR
          cases hE
          cases hO
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance kleeneTreeBoundaryBHistCarrier : BHistCarrier KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kleeneTreeBoundaryToEventFlow
  fromEventFlow := kleeneTreeBoundaryFromEventFlow

instance kleeneTreeBoundaryChapterTasteGate : ChapterTasteGate KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x
    exact kleeneTreeBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kleeneTreeBoundaryToEventFlow_injective heq)

instance kleeneTreeBoundaryFieldFaithful : FieldFaithful KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kleeneTreeBoundaryFields
  field_faithful := kleeneTreeBoundary_field_faithful

instance kleeneTreeBoundaryNontrivial :
    BEDC.Meta.TasteGate.Nontrivial KleeneTreeBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KleeneTreeBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KleeneTreeBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KleeneTreeBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kleeneTreeBoundaryChapterTasteGate

theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KleeneTreeBoundaryUp) ∧
      Nonempty (FieldFaithful KleeneTreeBoundaryUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial KleeneTreeBoundaryUp) ∧
          (∀ h : BHist,
            kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist h) = h) ∧
            (∀ x : KleeneTreeBoundaryUp,
              kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x) ∧
              (∀ x y : KleeneTreeBoundaryUp,
                kleeneTreeBoundaryToEventFlow x = kleeneTreeBoundaryToEventFlow y → x = y) ∧
                kleeneTreeBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨kleeneTreeBoundaryChapterTasteGate⟩
  · constructor
    · exact ⟨kleeneTreeBoundaryFieldFaithful⟩
    · constructor
      · exact ⟨kleeneTreeBoundaryNontrivial⟩
      · constructor
        · exact KleeneTreeBoundaryTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact kleeneTreeBoundary_round_trip
          · constructor
            · intro x y heq
              exact kleeneTreeBoundaryToEventFlow_injective heq
            · rfl

namespace TasteGate

theorem KleeneTreeBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KleeneTreeBoundaryUp) ∧
      Nonempty (FieldFaithful KleeneTreeBoundaryUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial KleeneTreeBoundaryUp) ∧
          (∀ h : BHist,
            kleeneTreeBoundaryDecodeBHist (kleeneTreeBoundaryEncodeBHist h) = h) ∧
            (∀ x : KleeneTreeBoundaryUp,
              kleeneTreeBoundaryFromEventFlow (kleeneTreeBoundaryToEventFlow x) = some x) ∧
              (∀ x y : KleeneTreeBoundaryUp,
                kleeneTreeBoundaryToEventFlow x = kleeneTreeBoundaryToEventFlow y → x = y) ∧
                kleeneTreeBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) :=
  BEDC.Derived.KleeneTreeBoundaryUp.KleeneTreeBoundaryTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.KleeneTreeBoundaryUp
