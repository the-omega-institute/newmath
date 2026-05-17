import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DefinitionTheoremProofAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DefinitionTheoremProofAuditUp : Type where
  | mk :
      (definitionDiscipline theoremDiscipline proofRoute scope refusal status transport
        continuation provenance name : BHist) →
      DefinitionTheoremProofAuditUp
  deriving DecidableEq

def definitionTheoremProofAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: definitionTheoremProofAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: definitionTheoremProofAuditEncodeBHist h

def definitionTheoremProofAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (definitionTheoremProofAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (definitionTheoremProofAuditDecodeBHist tail)

theorem DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      definitionTheoremProofAuditDecodeBHist (definitionTheoremProofAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def definitionTheoremProofAuditFields : DefinitionTheoremProofAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DefinitionTheoremProofAuditUp.mk definitionDiscipline theoremDiscipline proofRoute scope
      refusal status transport continuation provenance name =>
      [definitionDiscipline, theoremDiscipline, proofRoute, scope, refusal, status, transport,
        continuation, provenance, name]

def definitionTheoremProofAuditToEventFlow : DefinitionTheoremProofAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map definitionTheoremProofAuditEncodeBHist (definitionTheoremProofAuditFields x)

private def DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault index rest

def definitionTheoremProofAuditFromEventFlow : EventFlow → Option DefinitionTheoremProofAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (DefinitionTheoremProofAuditUp.mk
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 0 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 1 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 2 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 3 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 4 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 5 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 6 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 7 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 8 ef))
        (definitionTheoremProofAuditDecodeBHist
          (DefinitionTheoremProofAuditUp_single_carrier_alignment_eventAtDefault 9 ef)))

theorem DefinitionTheoremProofAuditUp_single_carrier_alignment_round_trip :
    ∀ x : DefinitionTheoremProofAuditUp,
      definitionTheoremProofAuditFromEventFlow (definitionTheoremProofAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk definitionDiscipline theoremDiscipline proofRoute scope refusal status transport
      continuation provenance name =>
      change
        some
          (DefinitionTheoremProofAuditUp.mk
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist definitionDiscipline))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist theoremDiscipline))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist proofRoute))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist scope))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist refusal))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist status))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist transport))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist continuation))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist provenance))
            (definitionTheoremProofAuditDecodeBHist
              (definitionTheoremProofAuditEncodeBHist name))) =
          some
            (DefinitionTheoremProofAuditUp.mk definitionDiscipline theoremDiscipline proofRoute
              scope refusal status transport continuation provenance name)
      rw [DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode definitionDiscipline,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode theoremDiscipline,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode proofRoute,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode scope,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode refusal,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode status,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode transport,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode continuation,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode provenance,
        DefinitionTheoremProofAuditUp_single_carrier_alignment_decode_encode name]

theorem DefinitionTheoremProofAuditUp_single_carrier_alignment_toEventFlow_injective
    {x y : DefinitionTheoremProofAuditUp} :
    definitionTheoremProofAuditToEventFlow x =
        definitionTheoremProofAuditToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      definitionTheoremProofAuditFromEventFlow (definitionTheoremProofAuditToEventFlow x) =
        definitionTheoremProofAuditFromEventFlow (definitionTheoremProofAuditToEventFlow y) :=
    congrArg definitionTheoremProofAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DefinitionTheoremProofAuditUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DefinitionTheoremProofAuditUp_single_carrier_alignment_round_trip y)))

private theorem definitionTheoremProofAudit_field_faithful :
    ∀ x y : DefinitionTheoremProofAuditUp,
      definitionTheoremProofAuditFields x = definitionTheoremProofAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk definitionDiscipline₁ theoremDiscipline₁ proofRoute₁ scope₁ refusal₁ status₁ transport₁
      continuation₁ provenance₁ name₁ =>
      cases y with
      | mk definitionDiscipline₂ theoremDiscipline₂ proofRoute₂ scope₂ refusal₂ status₂
          transport₂ continuation₂ provenance₂ name₂ =>
          cases h
          rfl

instance definitionTheoremProofAuditBHistCarrier :
    BHistCarrier DefinitionTheoremProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := definitionTheoremProofAuditToEventFlow
  fromEventFlow := definitionTheoremProofAuditFromEventFlow

instance definitionTheoremProofAuditChapterTasteGate :
    ChapterTasteGate DefinitionTheoremProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      definitionTheoremProofAuditFromEventFlow (definitionTheoremProofAuditToEventFlow x) =
        some x
    exact DefinitionTheoremProofAuditUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DefinitionTheoremProofAuditUp_single_carrier_alignment_toEventFlow_injective heq)

instance definitionTheoremProofAuditFieldFaithful :
    FieldFaithful DefinitionTheoremProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := definitionTheoremProofAuditFields
  field_faithful := definitionTheoremProofAudit_field_faithful

instance definitionTheoremProofAuditNontrivial : Nontrivial DefinitionTheoremProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DefinitionTheoremProofAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DefinitionTheoremProofAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DefinitionTheoremProofAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  definitionTheoremProofAuditChapterTasteGate

def taste_gate_witness : FieldFaithful DefinitionTheoremProofAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  definitionTheoremProofAuditFieldFaithful

theorem DefinitionTheoremProofAuditUp_single_carrier_alignment :
    (∀ x : DefinitionTheoremProofAuditUp,
      definitionTheoremProofAuditFromEventFlow (definitionTheoremProofAuditToEventFlow x) =
        some x) ∧
      (∀ x y : DefinitionTheoremProofAuditUp,
        definitionTheoremProofAuditToEventFlow x =
          definitionTheoremProofAuditToEventFlow y →
          x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DefinitionTheoremProofAuditUp_single_carrier_alignment_round_trip
  · intro x y heq
    exact DefinitionTheoremProofAuditUp_single_carrier_alignment_toEventFlow_injective heq

end BEDC.Derived.DefinitionTheoremProofAuditUp
