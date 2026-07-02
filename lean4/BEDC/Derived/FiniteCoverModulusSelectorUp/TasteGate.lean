import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverModulusSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverModulusSelectorUp : Type where
  | mk (K F R L U H C P N : BHist) : FiniteCoverModulusSelectorUp
  deriving DecidableEq

def finiteCoverModulusSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverModulusSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverModulusSelectorEncodeBHist h

def finiteCoverModulusSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverModulusSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverModulusSelectorDecodeBHist tail)

private theorem FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCoverModulusSelectorFields : FiniteCoverModulusSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverModulusSelectorUp.mk K F R L U H C P N => [K, F, R, L, U, H, C, P, N]

def finiteCoverModulusSelectorToEventFlow : FiniteCoverModulusSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteCoverModulusSelectorFields x).map finiteCoverModulusSelectorEncodeBHist

private def finiteCoverModulusSelectorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCoverModulusSelectorEventAt index rest

def finiteCoverModulusSelectorFromEventFlow (ef : EventFlow) :
    Option FiniteCoverModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteCoverModulusSelectorUp.mk
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 0 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 1 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 2 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 3 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 4 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 5 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 6 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 7 ef))
      (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEventAt 8 ef)))

private theorem FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_round_trip
    (x : FiniteCoverModulusSelectorUp) :
    finiteCoverModulusSelectorFromEventFlow (finiteCoverModulusSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F R L U H C P N =>
      change
        some
          (FiniteCoverModulusSelectorUp.mk
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist K))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist F))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist R))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist L))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist U))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist H))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist C))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist P))
            (finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist N))) =
          some (FiniteCoverModulusSelectorUp.mk K F R L U H C P N)
      rw [FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode K,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode F,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode R,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode L,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode U,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode H,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode C,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode P,
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteCoverModulusSelectorUp} :
    finiteCoverModulusSelectorToEventFlow x = finiteCoverModulusSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverModulusSelectorFromEventFlow (finiteCoverModulusSelectorToEventFlow x) =
        finiteCoverModulusSelectorFromEventFlow (finiteCoverModulusSelectorToEventFlow y) :=
    congrArg finiteCoverModulusSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteCoverModulusSelectorUp,
      finiteCoverModulusSelectorFields x = finiteCoverModulusSelectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ R₁ L₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ R₂ L₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance finiteCoverModulusSelectorBHistCarrier :
    BHistCarrier FiniteCoverModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverModulusSelectorToEventFlow
  fromEventFlow := finiteCoverModulusSelectorFromEventFlow

instance finiteCoverModulusSelectorChapterTasteGate :
    ChapterTasteGate FiniteCoverModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCoverModulusSelectorFromEventFlow (finiteCoverModulusSelectorToEventFlow x) = some x
    exact FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteCoverModulusSelectorFieldFaithful :
    FieldFaithful FiniteCoverModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteCoverModulusSelectorFields
  field_faithful := FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_fields_faithful

instance finiteCoverModulusSelectorNontrivial : Nontrivial FiniteCoverModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteCoverModulusSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteCoverModulusSelectorUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiniteCoverModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteCoverModulusSelectorChapterTasteGate

theorem FiniteCoverModulusSelectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteCoverModulusSelectorUp) ∧
      Nonempty (FieldFaithful FiniteCoverModulusSelectorUp) ∧
        Nonempty (Nontrivial FiniteCoverModulusSelectorUp) ∧
          (∀ h : BHist,
            finiteCoverModulusSelectorDecodeBHist (finiteCoverModulusSelectorEncodeBHist h) =
              h) ∧
            (∀ x : FiniteCoverModulusSelectorUp,
              finiteCoverModulusSelectorFromEventFlow
                  (finiteCoverModulusSelectorToEventFlow x) =
                some x) ∧
              (∀ x y : FiniteCoverModulusSelectorUp,
                finiteCoverModulusSelectorToEventFlow x =
                    finiteCoverModulusSelectorToEventFlow y →
                  x = y) ∧
                finiteCoverModulusSelectorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨finiteCoverModulusSelectorChapterTasteGate⟩,
      ⟨finiteCoverModulusSelectorFieldFaithful⟩,
      ⟨finiteCoverModulusSelectorNontrivial⟩,
      FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_decode_encode,
      FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteCoverModulusSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteCoverModulusSelectorUp
