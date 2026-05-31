import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireSteinhausUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireSteinhausUp : Type where
  | mk (baireCategory completeMetric normRow functionalAnalysis uniformBoundedness
      pointwiseLedger handoff transport replay provenance localName : BHist) :
      BaireSteinhausUp
  deriving DecidableEq

def baireSteinhausEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireSteinhausEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireSteinhausEncodeBHist h

def baireSteinhausDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireSteinhausDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireSteinhausDecodeBHist tail)

private theorem BaireSteinhausTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireSteinhausDecodeBHist (baireSteinhausEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireSteinhausFields : BaireSteinhausUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireSteinhausUp.mk baireCategory completeMetric normRow functionalAnalysis
      uniformBoundedness pointwiseLedger handoff transport replay provenance localName =>
      [baireCategory, completeMetric, normRow, functionalAnalysis, uniformBoundedness,
        pointwiseLedger, handoff, transport, replay, provenance, localName]

def baireSteinhausToEventFlow : BaireSteinhausUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (baireSteinhausFields x).map baireSteinhausEncodeBHist

def baireSteinhausFromEventFlow : EventFlow → Option BaireSteinhausUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | baireCategory :: completeMetric :: normRow :: functionalAnalysis ::
        uniformBoundedness :: pointwiseLedger :: handoff :: transport :: replay ::
        provenance :: localName :: [] =>
        some
          (BaireSteinhausUp.mk
            (baireSteinhausDecodeBHist baireCategory)
            (baireSteinhausDecodeBHist completeMetric)
            (baireSteinhausDecodeBHist normRow)
            (baireSteinhausDecodeBHist functionalAnalysis)
            (baireSteinhausDecodeBHist uniformBoundedness)
            (baireSteinhausDecodeBHist pointwiseLedger)
            (baireSteinhausDecodeBHist handoff)
            (baireSteinhausDecodeBHist transport)
            (baireSteinhausDecodeBHist replay)
            (baireSteinhausDecodeBHist provenance)
            (baireSteinhausDecodeBHist localName))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

instance baireSteinhausBHistCarrier : BHistCarrier BaireSteinhausUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireSteinhausToEventFlow
  fromEventFlow := baireSteinhausFromEventFlow

private theorem baireSteinhaus_round_trip :
    ∀ x : BaireSteinhausUp, baireSteinhausFromEventFlow (baireSteinhausToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk baireCategory completeMetric normRow functionalAnalysis uniformBoundedness
      pointwiseLedger handoff transport replay provenance localName =>
      change
        some
            (BaireSteinhausUp.mk
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist baireCategory))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist completeMetric))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist normRow))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist functionalAnalysis))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist uniformBoundedness))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist pointwiseLedger))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist handoff))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist transport))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist replay))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist provenance))
              (baireSteinhausDecodeBHist (baireSteinhausEncodeBHist localName))) =
          some
            (BaireSteinhausUp.mk baireCategory completeMetric normRow functionalAnalysis
              uniformBoundedness pointwiseLedger handoff transport replay provenance localName)
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode baireCategory]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode completeMetric]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode normRow]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode functionalAnalysis]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode uniformBoundedness]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode pointwiseLedger]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode handoff]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode transport]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode replay]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [BaireSteinhausTasteGate_single_carrier_alignment_decode_encode localName]

private theorem baireSteinhausToEventFlow_injective {x y : BaireSteinhausUp} :
    baireSteinhausToEventFlow x = baireSteinhausToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = baireSteinhausFromEventFlow (baireSteinhausToEventFlow x) :=
        (baireSteinhaus_round_trip x).symm
      _ = baireSteinhausFromEventFlow (baireSteinhausToEventFlow y) :=
        congrArg baireSteinhausFromEventFlow hxy
      _ = some y := baireSteinhaus_round_trip y
  exact Option.some.inj optionEq

private theorem baireSteinhaus_field_faithful :
    ∀ x y : BaireSteinhausUp, baireSteinhausFields x = baireSteinhausFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk baireCategory₁ completeMetric₁ normRow₁ functionalAnalysis₁ uniformBoundedness₁
      pointwiseLedger₁ handoff₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk baireCategory₂ completeMetric₂ normRow₂ functionalAnalysis₂ uniformBoundedness₂
          pointwiseLedger₂ handoff₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance baireSteinhausChapterTasteGate : ChapterTasteGate BaireSteinhausUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireSteinhausFromEventFlow (baireSteinhausToEventFlow x) = some x
    exact baireSteinhaus_round_trip x
  layer_separation := by
    intro x y hxy heq
    apply hxy
    exact baireSteinhausToEventFlow_injective heq

instance baireSteinhausFieldFaithful : FieldFaithful BaireSteinhausUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireSteinhausFields
  field_faithful := baireSteinhaus_field_faithful

instance baireSteinhausNontrivial : Nontrivial BaireSteinhausUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireSteinhausUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireSteinhausUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BaireSteinhausUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireSteinhausChapterTasteGate

def taste_gate_witness : FieldFaithful BaireSteinhausUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireSteinhausFieldFaithful

theorem BaireSteinhausTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireSteinhausUp) ∧
      Nonempty (FieldFaithful BaireSteinhausUp) ∧
        Nonempty (Nontrivial BaireSteinhausUp) ∧
          (∀ h : BHist, baireSteinhausDecodeBHist (baireSteinhausEncodeBHist h) = h) ∧
            (∀ x : BaireSteinhausUp,
              baireSteinhausFromEventFlow (baireSteinhausToEventFlow x) = some x) ∧
              (∀ x y : BaireSteinhausUp,
                baireSteinhausToEventFlow x = baireSteinhausToEventFlow y → x = y) ∧
                baireSteinhausEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨baireSteinhausChapterTasteGate⟩,
      ⟨⟨baireSteinhausFieldFaithful⟩,
        ⟨⟨baireSteinhausNontrivial⟩,
          BaireSteinhausTasteGate_single_carrier_alignment_decode_encode,
          baireSteinhaus_round_trip,
          (fun _ _ heq => baireSteinhausToEventFlow_injective heq),
          rfl⟩⟩⟩

end BEDC.Derived.BaireSteinhausUp
