import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerOperationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerOperationUp : Type where
  | mk (T O M W R E H C P N : BHist) : BrouwerOperationUp
  deriving DecidableEq

def brouwerOperationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerOperationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerOperationEncodeBHist h

def brouwerOperationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerOperationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerOperationDecodeBHist tail)

private theorem BrouwerOperationTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist, brouwerOperationDecodeBHist (brouwerOperationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerOperationFields : BrouwerOperationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerOperationUp.mk T O M W R E H C P N => [T, O, M, W, R, E, H, C, P, N]

def brouwerOperationToEventFlow : BrouwerOperationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (brouwerOperationFields x).map brouwerOperationEncodeBHist

private def brouwerOperationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerOperationEventAtDefault index rest

def brouwerOperationFromEventFlow (ef : EventFlow) : Option BrouwerOperationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerOperationUp.mk
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 0 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 1 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 2 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 3 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 4 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 5 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 6 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 7 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 8 ef))
      (brouwerOperationDecodeBHist (brouwerOperationEventAtDefault 9 ef)))

private theorem BrouwerOperationTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : BrouwerOperationUp,
      brouwerOperationFromEventFlow (brouwerOperationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T O M W R E H C P N =>
      change
        some
          (BrouwerOperationUp.mk
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist T))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist O))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist M))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist W))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist R))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist E))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist H))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist C))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist P))
            (brouwerOperationDecodeBHist (brouwerOperationEncodeBHist N))) =
          some (BrouwerOperationUp.mk T O M W R E H C P N)
      rw [BrouwerOperationTasteGate_single_carrier_alignment_decode_aux T,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux O,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux M,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux W,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux R,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux E,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux H,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux C,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux P,
        BrouwerOperationTasteGate_single_carrier_alignment_decode_aux N]

private theorem BrouwerOperationTasteGate_single_carrier_alignment_injective_aux
    {x y : BrouwerOperationUp} :
    brouwerOperationToEventFlow x = brouwerOperationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerOperationFromEventFlow (brouwerOperationToEventFlow x) =
        brouwerOperationFromEventFlow (brouwerOperationToEventFlow y) :=
    congrArg brouwerOperationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BrouwerOperationTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread
        (BrouwerOperationTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem BrouwerOperationTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : BrouwerOperationUp, brouwerOperationFields x = brouwerOperationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ O₁ M₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ O₂ M₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance brouwerOperationBHistCarrier : BHistCarrier BrouwerOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerOperationToEventFlow
  fromEventFlow := brouwerOperationFromEventFlow

instance brouwerOperationChapterTasteGate : ChapterTasteGate BrouwerOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerOperationFromEventFlow (brouwerOperationToEventFlow x) = some x
    exact BrouwerOperationTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BrouwerOperationTasteGate_single_carrier_alignment_injective_aux heq)

instance brouwerOperationFieldFaithful : FieldFaithful BrouwerOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := brouwerOperationFields
  field_faithful := by
    intro x y hfields
    exact BrouwerOperationTasteGate_single_carrier_alignment_fields_aux x y hfields

instance brouwerOperationNontrivial : Nontrivial BrouwerOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BrouwerOperationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BrouwerOperationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

namespace TasteGate

theorem BrouwerOperationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BrouwerOperationUp) ∧
      Nonempty (FieldFaithful BrouwerOperationUp) ∧
        Nonempty (Nontrivial BrouwerOperationUp) ∧
          (∀ h : BHist, brouwerOperationDecodeBHist (brouwerOperationEncodeBHist h) = h) ∧
            (∀ x : BrouwerOperationUp,
              brouwerOperationFromEventFlow (brouwerOperationToEventFlow x) = some x) ∧
              (∀ x y : BrouwerOperationUp,
                brouwerOperationToEventFlow x = brouwerOperationToEventFlow y → x = y) ∧
                brouwerOperationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨brouwerOperationChapterTasteGate⟩
  · constructor
    · exact ⟨brouwerOperationFieldFaithful⟩
    · constructor
      · exact ⟨brouwerOperationNontrivial⟩
      · constructor
        · exact BrouwerOperationTasteGate_single_carrier_alignment_decode_aux
        · constructor
          · exact BrouwerOperationTasteGate_single_carrier_alignment_round_trip_aux
          · constructor
            · intro x y heq
              exact BrouwerOperationTasteGate_single_carrier_alignment_injective_aux heq
            · rfl

end TasteGate

end BEDC.Derived.BrouwerOperationUp
