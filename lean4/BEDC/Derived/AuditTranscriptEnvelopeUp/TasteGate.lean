import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditTranscriptEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditTranscriptEnvelopeUp : Type where
  | mk :
      (claimKind carrier ledger status gap anchor replay notClaimed transport route provenance
        name : BHist) →
      AuditTranscriptEnvelopeUp
  deriving DecidableEq

def auditTranscriptEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditTranscriptEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditTranscriptEnvelopeEncodeBHist h

def auditTranscriptEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditTranscriptEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditTranscriptEnvelopeDecodeBHist tail)

private theorem auditTranscriptEnvelope_decode_encode_bhist :
    ∀ h : BHist,
      auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditTranscriptEnvelopeFields : AuditTranscriptEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditTranscriptEnvelopeUp.mk claimKind carrier ledger status gap anchor replay notClaimed
      transport route provenance name =>
      [claimKind, carrier, ledger, status, gap, anchor, replay, notClaimed, transport, route,
        provenance, name]

def auditTranscriptEnvelopeToEventFlow : AuditTranscriptEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditTranscriptEnvelopeUp.mk claimKind carrier ledger status gap anchor replay notClaimed
      transport route provenance name =>
      [[BMark.b0], auditTranscriptEnvelopeEncodeBHist claimKind,
        [BMark.b1, BMark.b0], auditTranscriptEnvelopeEncodeBHist carrier,
        [BMark.b1, BMark.b1, BMark.b0], auditTranscriptEnvelopeEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist status,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist anchor,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditTranscriptEnvelopeEncodeBHist notClaimed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist name]

private def auditTranscriptEnvelopeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => auditTranscriptEnvelopeEventAtDefault index rest

def auditTranscriptEnvelopeFromEventFlow (ef : EventFlow) :
    Option AuditTranscriptEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AuditTranscriptEnvelopeUp.mk
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 1 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 3 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 5 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 7 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 9 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 11 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 13 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 15 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 17 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 19 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 21 ef))
      (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEventAtDefault 23 ef)))

private theorem auditTranscriptEnvelope_round_trip :
    ∀ x : AuditTranscriptEnvelopeUp,
      auditTranscriptEnvelopeFromEventFlow (auditTranscriptEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claimKind carrier ledger status gap anchor replay notClaimed transport route provenance
      name =>
      change
        some
          (AuditTranscriptEnvelopeUp.mk
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist claimKind))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist carrier))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist ledger))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist status))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist gap))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist anchor))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist replay))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist notClaimed))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist transport))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist route))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist provenance))
            (auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist name))) =
          some
            (AuditTranscriptEnvelopeUp.mk claimKind carrier ledger status gap anchor replay
              notClaimed transport route provenance name)
      rw [auditTranscriptEnvelope_decode_encode_bhist claimKind,
        auditTranscriptEnvelope_decode_encode_bhist carrier,
        auditTranscriptEnvelope_decode_encode_bhist ledger,
        auditTranscriptEnvelope_decode_encode_bhist status,
        auditTranscriptEnvelope_decode_encode_bhist gap,
        auditTranscriptEnvelope_decode_encode_bhist anchor,
        auditTranscriptEnvelope_decode_encode_bhist replay,
        auditTranscriptEnvelope_decode_encode_bhist notClaimed,
        auditTranscriptEnvelope_decode_encode_bhist transport,
        auditTranscriptEnvelope_decode_encode_bhist route,
        auditTranscriptEnvelope_decode_encode_bhist provenance,
        auditTranscriptEnvelope_decode_encode_bhist name]

private theorem auditTranscriptEnvelopeToEventFlow_injective {x y : AuditTranscriptEnvelopeUp} :
    auditTranscriptEnvelopeToEventFlow x = auditTranscriptEnvelopeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditTranscriptEnvelopeFromEventFlow (auditTranscriptEnvelopeToEventFlow x) =
        auditTranscriptEnvelopeFromEventFlow (auditTranscriptEnvelopeToEventFlow y) :=
    congrArg auditTranscriptEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditTranscriptEnvelope_round_trip x).symm
      (Eq.trans hread (auditTranscriptEnvelope_round_trip y)))

private theorem auditTranscriptEnvelope_field_faithful :
    ∀ x y : AuditTranscriptEnvelopeUp,
      auditTranscriptEnvelopeFields x = auditTranscriptEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk claimKind₁ carrier₁ ledger₁ status₁ gap₁ anchor₁ replay₁ notClaimed₁ transport₁
      route₁ provenance₁ name₁ =>
      cases y with
      | mk claimKind₂ carrier₂ ledger₂ status₂ gap₂ anchor₂ replay₂ notClaimed₂ transport₂
          route₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance auditTranscriptEnvelopeBHistCarrier : BHistCarrier AuditTranscriptEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditTranscriptEnvelopeToEventFlow
  fromEventFlow := auditTranscriptEnvelopeFromEventFlow

instance auditTranscriptEnvelopeChapterTasteGate :
    ChapterTasteGate AuditTranscriptEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditTranscriptEnvelopeFromEventFlow (auditTranscriptEnvelopeToEventFlow x) = some x
    exact auditTranscriptEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditTranscriptEnvelopeToEventFlow_injective heq)

instance auditTranscriptEnvelopeFieldFaithful : FieldFaithful AuditTranscriptEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditTranscriptEnvelopeFields
  field_faithful := auditTranscriptEnvelope_field_faithful

instance auditTranscriptEnvelopeNontrivial : Nontrivial AuditTranscriptEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditTranscriptEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AuditTranscriptEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditTranscriptEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditTranscriptEnvelopeChapterTasteGate

end BEDC.Derived.AuditTranscriptEnvelopeUp
