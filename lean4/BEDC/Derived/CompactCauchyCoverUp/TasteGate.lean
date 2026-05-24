import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCauchyCoverUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactCauchyCoverUp : Type where
  | mk (M W D S R E H C P N : BHist) : CompactCauchyCoverUp
  deriving DecidableEq

def compactCauchyCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCauchyCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCauchyCoverEncodeBHist h

def compactCauchyCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCauchyCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCauchyCoverDecodeBHist tail)

private theorem CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactCauchyCoverFields : CompactCauchyCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactCauchyCoverUp.mk M W D S R E H C P N => [M, W, D, S, R, E, H, C, P, N]

def compactCauchyCoverToEventFlow : CompactCauchyCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactCauchyCoverFields x).map compactCauchyCoverEncodeBHist

private def compactCauchyCoverEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactCauchyCoverEventAt index rest

def compactCauchyCoverFromEventFlow (ef : EventFlow) :
    Option CompactCauchyCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactCauchyCoverUp.mk
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 0 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 1 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 2 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 3 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 4 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 5 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 6 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 7 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 8 ef))
      (compactCauchyCoverDecodeBHist (compactCauchyCoverEventAt 9 ef)))

private theorem CompactCauchyCoverTasteGate_single_carrier_alignment_round_trip
    (x : CompactCauchyCoverUp) :
    compactCauchyCoverFromEventFlow (compactCauchyCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M W D S R E H C P N =>
      change
        some
          (CompactCauchyCoverUp.mk
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist M))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist W))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist D))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist S))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist R))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist E))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist H))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist C))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist P))
            (compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist N))) =
          some (CompactCauchyCoverUp.mk M W D S R E H C P N)
      rw [CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode M,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode W,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode D,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode S,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode R,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode E,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode H,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode C,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode P,
        CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactCauchyCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactCauchyCoverUp} :
    compactCauchyCoverToEventFlow x = compactCauchyCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactCauchyCoverFromEventFlow (compactCauchyCoverToEventFlow x) =
        compactCauchyCoverFromEventFlow (compactCauchyCoverToEventFlow y) :=
    congrArg compactCauchyCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactCauchyCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactCauchyCoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactCauchyCoverTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompactCauchyCoverUp,
      compactCauchyCoverFields x = compactCauchyCoverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ W₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ W₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactCauchyCoverBHistCarrier : BHistCarrier CompactCauchyCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactCauchyCoverToEventFlow
  fromEventFlow := compactCauchyCoverFromEventFlow

instance compactCauchyCoverChapterTasteGate : ChapterTasteGate CompactCauchyCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactCauchyCoverFromEventFlow (compactCauchyCoverToEventFlow x) = some x
    exact CompactCauchyCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactCauchyCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactCauchyCoverFieldFaithful :
    FieldFaithful CompactCauchyCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactCauchyCoverFields
  field_faithful := CompactCauchyCoverTasteGate_single_carrier_alignment_fields_faithful

instance compactCauchyCoverNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactCauchyCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactCauchyCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactCauchyCoverUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CompactCauchyCoverTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompactCauchyCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactCauchyCoverChapterTasteGate

theorem CompactCauchyCoverTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactCauchyCoverUp) ∧
      Nonempty (FieldFaithful CompactCauchyCoverUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactCauchyCoverUp) ∧
          (∀ h : BHist,
            compactCauchyCoverDecodeBHist (compactCauchyCoverEncodeBHist h) = h) ∧
            (∀ x : CompactCauchyCoverUp,
              compactCauchyCoverFromEventFlow (compactCauchyCoverToEventFlow x) = some x) ∧
              (∀ x y : CompactCauchyCoverUp,
                compactCauchyCoverToEventFlow x = compactCauchyCoverToEventFlow y → x = y) ∧
                compactCauchyCoverEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨compactCauchyCoverChapterTasteGate⟩,
      ⟨compactCauchyCoverFieldFaithful⟩,
      ⟨compactCauchyCoverNontrivial⟩,
      CompactCauchyCoverTasteGate_single_carrier_alignment_decode_encode,
      CompactCauchyCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompactCauchyCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactCauchyCoverUp.TasteGate
