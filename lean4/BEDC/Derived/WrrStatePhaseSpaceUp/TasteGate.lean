import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WrrStatePhaseSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WrrStatePhaseSpaceUp : Type where
  | mk (S A V R T H C P N : BHist) : WrrStatePhaseSpaceUp
  deriving DecidableEq

def wrrStatePhaseSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wrrStatePhaseSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wrrStatePhaseSpaceEncodeBHist h

def wrrStatePhaseSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wrrStatePhaseSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wrrStatePhaseSpaceDecodeBHist tail)

private theorem WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def wrrStatePhaseSpaceFields : WrrStatePhaseSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WrrStatePhaseSpaceUp.mk S A V R T H C P N => [S, A, V, R, T, H, C, P, N]

def wrrStatePhaseSpaceToEventFlow : WrrStatePhaseSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (wrrStatePhaseSpaceFields x).map wrrStatePhaseSpaceEncodeBHist

private def wrrStatePhaseSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => wrrStatePhaseSpaceEventAt index rest

def wrrStatePhaseSpaceFromEventFlow (ef : EventFlow) :
    Option WrrStatePhaseSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WrrStatePhaseSpaceUp.mk
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 0 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 1 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 2 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 3 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 4 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 5 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 6 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 7 ef))
      (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEventAt 8 ef)))

private theorem WrrStatePhaseSpaceTasteGate_single_carrier_alignment_round_trip
    (x : WrrStatePhaseSpaceUp) :
    wrrStatePhaseSpaceFromEventFlow (wrrStatePhaseSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A V R T H C P N =>
      change
        some
          (WrrStatePhaseSpaceUp.mk
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist S))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist A))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist V))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist R))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist T))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist H))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist C))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist P))
            (wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist N))) =
          some (WrrStatePhaseSpaceUp.mk S A V R T H C P N)
      rw [WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode S,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode A,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode V,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode R,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode T,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode H,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode C,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode P,
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem WrrStatePhaseSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WrrStatePhaseSpaceUp} :
    wrrStatePhaseSpaceToEventFlow x = wrrStatePhaseSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      wrrStatePhaseSpaceFromEventFlow (wrrStatePhaseSpaceToEventFlow x) =
        wrrStatePhaseSpaceFromEventFlow (wrrStatePhaseSpaceToEventFlow y) :=
    congrArg wrrStatePhaseSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WrrStatePhaseSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WrrStatePhaseSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem WrrStatePhaseSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : WrrStatePhaseSpaceUp,
      wrrStatePhaseSpaceFields x = wrrStatePhaseSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ A₁ V₁ R₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ A₂ V₂ R₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance wrrStatePhaseSpaceBHistCarrier : BHistCarrier WrrStatePhaseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wrrStatePhaseSpaceToEventFlow
  fromEventFlow := wrrStatePhaseSpaceFromEventFlow

instance wrrStatePhaseSpaceChapterTasteGate :
    ChapterTasteGate WrrStatePhaseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change wrrStatePhaseSpaceFromEventFlow (wrrStatePhaseSpaceToEventFlow x) = some x
    exact WrrStatePhaseSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WrrStatePhaseSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance wrrStatePhaseSpaceFieldFaithful :
    FieldFaithful WrrStatePhaseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := wrrStatePhaseSpaceFields
  field_faithful := WrrStatePhaseSpaceTasteGate_single_carrier_alignment_fields_faithful

instance wrrStatePhaseSpaceNontrivial : Nontrivial WrrStatePhaseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WrrStatePhaseSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WrrStatePhaseSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem WrrStatePhaseSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate WrrStatePhaseSpaceUp) ∧
      Nonempty (FieldFaithful WrrStatePhaseSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial WrrStatePhaseSpaceUp) ∧
          (∀ h : BHist,
            wrrStatePhaseSpaceDecodeBHist (wrrStatePhaseSpaceEncodeBHist h) = h) ∧
            (∀ x : WrrStatePhaseSpaceUp,
              wrrStatePhaseSpaceFromEventFlow (wrrStatePhaseSpaceToEventFlow x) = some x) ∧
              (∀ x y : WrrStatePhaseSpaceUp,
                wrrStatePhaseSpaceToEventFlow x = wrrStatePhaseSpaceToEventFlow y →
                  x = y) ∧
                wrrStatePhaseSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro wrrStatePhaseSpaceChapterTasteGate,
      Nonempty.intro wrrStatePhaseSpaceFieldFaithful,
      Nonempty.intro wrrStatePhaseSpaceNontrivial,
      WrrStatePhaseSpaceTasteGate_single_carrier_alignment_decode_encode,
      WrrStatePhaseSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        WrrStatePhaseSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.WrrStatePhaseSpaceUp
