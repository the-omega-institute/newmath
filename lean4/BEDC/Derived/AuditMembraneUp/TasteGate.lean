import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMembraneUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMembraneUp : Type where
  | mk :
      (gate boundary refusal drift transport replay provenance localCert : BHist) →
      AuditMembraneUp
  deriving DecidableEq

def auditMembraneEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMembraneEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMembraneEncodeBHist h

def auditMembraneDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMembraneDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMembraneDecodeBHist tail)

theorem AuditMembraneTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, auditMembraneDecodeBHist (auditMembraneEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditMembraneFields : AuditMembraneUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMembraneUp.mk gate boundary refusal drift transport replay provenance localCert =>
      [gate, boundary, refusal, drift, transport, replay, provenance, localCert]

def auditMembraneToEventFlow : AuditMembraneUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map auditMembraneEncodeBHist (auditMembraneFields x)

private def AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault index rest

def auditMembraneFromEventFlow : EventFlow → Option AuditMembraneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AuditMembraneUp.mk
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (auditMembraneDecodeBHist
          (AuditMembraneTasteGate_single_carrier_alignment_eventAtDefault 7 ef)))

theorem AuditMembraneTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AuditMembraneUp,
      auditMembraneFromEventFlow (auditMembraneToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gate boundary refusal drift transport replay provenance localCert =>
      change
        some
          (AuditMembraneUp.mk
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist gate))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist boundary))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist refusal))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist drift))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist transport))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist replay))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist provenance))
            (auditMembraneDecodeBHist (auditMembraneEncodeBHist localCert))) =
          some
            (AuditMembraneUp.mk gate boundary refusal drift transport replay provenance localCert)
      rw [AuditMembraneTasteGate_single_carrier_alignment_decode_encode gate,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode boundary,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode refusal,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode drift,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode transport,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode replay,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode provenance,
        AuditMembraneTasteGate_single_carrier_alignment_decode_encode localCert]

theorem AuditMembraneTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AuditMembraneUp} :
    auditMembraneToEventFlow x = auditMembraneToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMembraneFromEventFlow (auditMembraneToEventFlow x) =
        auditMembraneFromEventFlow (auditMembraneToEventFlow y) :=
    congrArg auditMembraneFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AuditMembraneTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AuditMembraneTasteGate_single_carrier_alignment_round_trip y)))

private theorem auditMembrane_field_faithful :
    ∀ x y : AuditMembraneUp, auditMembraneFields x = auditMembraneFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk gate₁ boundary₁ refusal₁ drift₁ transport₁ replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk gate₂ boundary₂ refusal₂ drift₂ transport₂ replay₂ provenance₂ localCert₂ =>
          cases h
          rfl

instance auditMembraneBHistCarrier : BHistCarrier AuditMembraneUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMembraneToEventFlow
  fromEventFlow := auditMembraneFromEventFlow

instance auditMembraneChapterTasteGate : ChapterTasteGate AuditMembraneUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMembraneFromEventFlow (auditMembraneToEventFlow x) = some x
    exact AuditMembraneTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AuditMembraneTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance auditMembraneFieldFaithful : FieldFaithful AuditMembraneUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMembraneFields
  field_faithful := auditMembrane_field_faithful

instance auditMembraneNontrivial : Nontrivial AuditMembraneUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMembraneUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AuditMembraneUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditMembraneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMembraneChapterTasteGate

theorem AuditMembraneTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AuditMembraneUp) ∧
      Nonempty (FieldFaithful AuditMembraneUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial AuditMembraneUp) ∧
      (∀ h : BHist, auditMembraneDecodeBHist (auditMembraneEncodeBHist h) = h) ∧
      (∀ x : AuditMembraneUp,
        auditMembraneFromEventFlow (auditMembraneToEventFlow x) = some x) ∧
      (∀ x y : AuditMembraneUp,
        auditMembraneToEventFlow x = auditMembraneToEventFlow y → x = y) ∧
      auditMembraneEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro auditMembraneChapterTasteGate
  · constructor
    · exact Nonempty.intro auditMembraneFieldFaithful
    · constructor
      · exact Nonempty.intro auditMembraneNontrivial
      · constructor
        · exact AuditMembraneTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact AuditMembraneTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact AuditMembraneTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.AuditMembraneUp
