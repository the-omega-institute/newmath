import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireSpaceUp : Type where
  | mk : (schedule prefixWindow classifier localLedger provenance : BHist) → BaireSpaceUp
  deriving DecidableEq

def baireSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireSpaceEncodeBHist h

def baireSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireSpaceDecodeBHist tail)

private theorem BaireSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireSpaceDecodeBHist (baireSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireSpaceFields : BaireSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireSpaceUp.mk schedule prefixWindow classifier localLedger provenance =>
      [schedule, prefixWindow, classifier, localLedger, provenance]

def baireSpaceToEventFlow : BaireSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireSpaceFields x).map baireSpaceEncodeBHist

private def baireSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireSpaceEventAt index rest

def baireSpaceFromEventFlow (ef : EventFlow) : Option BaireSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireSpaceUp.mk
      (baireSpaceDecodeBHist (baireSpaceEventAt 0 ef))
      (baireSpaceDecodeBHist (baireSpaceEventAt 1 ef))
      (baireSpaceDecodeBHist (baireSpaceEventAt 2 ef))
      (baireSpaceDecodeBHist (baireSpaceEventAt 3 ef))
      (baireSpaceDecodeBHist (baireSpaceEventAt 4 ef)))

private theorem BaireSpaceTasteGate_single_carrier_alignment_round_trip
    (x : BaireSpaceUp) :
    baireSpaceFromEventFlow (baireSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk schedule prefixWindow classifier localLedger provenance =>
      change
        some
          (BaireSpaceUp.mk
            (baireSpaceDecodeBHist (baireSpaceEncodeBHist schedule))
            (baireSpaceDecodeBHist (baireSpaceEncodeBHist prefixWindow))
            (baireSpaceDecodeBHist (baireSpaceEncodeBHist classifier))
            (baireSpaceDecodeBHist (baireSpaceEncodeBHist localLedger))
            (baireSpaceDecodeBHist (baireSpaceEncodeBHist provenance))) =
          some (BaireSpaceUp.mk schedule prefixWindow classifier localLedger provenance)
      rw [BaireSpaceTasteGate_single_carrier_alignment_decode_encode schedule,
        BaireSpaceTasteGate_single_carrier_alignment_decode_encode prefixWindow,
        BaireSpaceTasteGate_single_carrier_alignment_decode_encode classifier,
        BaireSpaceTasteGate_single_carrier_alignment_decode_encode localLedger,
        BaireSpaceTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem BaireSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireSpaceUp} :
    baireSpaceToEventFlow x = baireSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireSpaceFromEventFlow (baireSpaceToEventFlow x) =
        baireSpaceFromEventFlow (baireSpaceToEventFlow y) :=
    congrArg baireSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BaireSpaceUp, baireSpaceFields x = baireSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk schedule₁ prefixWindow₁ classifier₁ localLedger₁ provenance₁ =>
      cases y with
      | mk schedule₂ prefixWindow₂ classifier₂ localLedger₂ provenance₂ =>
          cases hfields
          rfl

instance baireSpaceBHistCarrier : BHistCarrier BaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireSpaceToEventFlow
  fromEventFlow := baireSpaceFromEventFlow

instance baireSpaceChapterTasteGate : ChapterTasteGate BaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireSpaceFromEventFlow (baireSpaceToEventFlow x) = some x
    exact BaireSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance baireSpaceFieldFaithful : FieldFaithful BaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireSpaceFields
  field_faithful := BaireSpaceTasteGate_single_carrier_alignment_fields_faithful

instance baireSpaceNontrivial : Nontrivial BaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BaireSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem BaireSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireSpaceUp) ∧ Nonempty (FieldFaithful BaireSpaceUp) ∧
      Nonempty (Nontrivial BaireSpaceUp) ∧
        (∀ h : BHist, baireSpaceDecodeBHist (baireSpaceEncodeBHist h) = h) ∧
          (∀ x : BaireSpaceUp, baireSpaceFromEventFlow (baireSpaceToEventFlow x) =
            some x) ∧
            (∀ x y : BaireSpaceUp,
              baireSpaceToEventFlow x = baireSpaceToEventFlow y → x = y) ∧
              baireSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨baireSpaceChapterTasteGate⟩
  · constructor
    · exact ⟨baireSpaceFieldFaithful⟩
    · constructor
      · exact ⟨baireSpaceNontrivial⟩
      · constructor
        · exact BaireSpaceTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · intro x
            exact BaireSpaceTasteGate_single_carrier_alignment_round_trip x
          · constructor
            · intro x y heq
              exact BaireSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.BaireSpaceUp.TasteGate
