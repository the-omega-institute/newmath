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
        nameCert : BHist) →
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

private theorem auditTranscriptEnvelopeDecode_encode_bhist :
    ∀ h : BHist,
      auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditTranscriptEnvelopeToEventFlow : AuditTranscriptEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditTranscriptEnvelopeUp.mk claimKind carrier ledger status gap anchor replay notClaimed
      transport route provenance nameCert =>
      [[BMark.b0],
        auditTranscriptEnvelopeEncodeBHist claimKind,
        [BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist carrier,
        [BMark.b1, BMark.b1, BMark.b0],
        auditTranscriptEnvelopeEncodeBHist ledger,
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
        auditTranscriptEnvelopeEncodeBHist nameCert]

def auditTranscriptEnvelopeFromEventFlow : EventFlow → Option AuditTranscriptEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | claimKind :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | carrier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | status :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gap :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | anchor :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | notClaimed :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | route :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | provenance ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | nameCert ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (AuditTranscriptEnvelopeUp.mk
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            claimKind)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            carrier)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            ledger)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            status)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            gap)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            anchor)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            replay)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            notClaimed)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            transport)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            route)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            provenance)
                                                                                                          (auditTranscriptEnvelopeDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ ::
                                                                                                      _ =>
                                                                                                      none

private theorem auditTranscriptEnvelope_round_trip :
    ∀ x : AuditTranscriptEnvelopeUp,
      auditTranscriptEnvelopeFromEventFlow (auditTranscriptEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claimKind carrier ledger status gap anchor replay notClaimed transport route provenance
      nameCert =>
      change
        some
          (AuditTranscriptEnvelopeUp.mk
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist claimKind))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist carrier))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist ledger))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist status))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist gap))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist anchor))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist replay))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist notClaimed))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist transport))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist route))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist provenance))
            (auditTranscriptEnvelopeDecodeBHist
              (auditTranscriptEnvelopeEncodeBHist nameCert))) =
          some
            (AuditTranscriptEnvelopeUp.mk claimKind carrier ledger status gap anchor replay
              notClaimed transport route provenance nameCert)
      rw [auditTranscriptEnvelopeDecode_encode_bhist claimKind,
        auditTranscriptEnvelopeDecode_encode_bhist carrier,
        auditTranscriptEnvelopeDecode_encode_bhist ledger,
        auditTranscriptEnvelopeDecode_encode_bhist status,
        auditTranscriptEnvelopeDecode_encode_bhist gap,
        auditTranscriptEnvelopeDecode_encode_bhist anchor,
        auditTranscriptEnvelopeDecode_encode_bhist replay,
        auditTranscriptEnvelopeDecode_encode_bhist notClaimed,
        auditTranscriptEnvelopeDecode_encode_bhist transport,
        auditTranscriptEnvelopeDecode_encode_bhist route,
        auditTranscriptEnvelopeDecode_encode_bhist provenance,
        auditTranscriptEnvelopeDecode_encode_bhist nameCert]

private theorem auditTranscriptEnvelopeToEventFlow_injective
    {x y : AuditTranscriptEnvelopeUp} :
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
  fields := fun x =>
    match x with
    | AuditTranscriptEnvelopeUp.mk claimKind carrier ledger status gap anchor replay notClaimed
        transport route provenance nameCert =>
        [claimKind, carrier, ledger, status, gap, anchor, replay, notClaimed, transport,
          route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk claimKind₁ carrier₁ ledger₁ status₁ gap₁ anchor₁ replay₁ notClaimed₁ transport₁
        route₁ provenance₁ nameCert₁ =>
        cases y with
        | mk claimKind₂ carrier₂ ledger₂ status₂ gap₂ anchor₂ replay₂ notClaimed₂ transport₂
            route₂ provenance₂ nameCert₂ =>
            cases h
            rfl

instance auditTranscriptEnvelopeNontrivial : Nontrivial AuditTranscriptEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditTranscriptEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditTranscriptEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditTranscriptEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditTranscriptEnvelopeChapterTasteGate

theorem AuditTranscriptEnvelopeTasteGate_single_carrier_alignment
    {K C L S G A R U H T P N : BHist} :
    (∀ h : BHist,
        auditTranscriptEnvelopeDecodeBHist (auditTranscriptEnvelopeEncodeBHist h) = h) ∧
      (auditTranscriptEnvelopeFromEventFlow
          (auditTranscriptEnvelopeToEventFlow
            (AuditTranscriptEnvelopeUp.mk K C L S G A R U H T P N)) =
        some (AuditTranscriptEnvelopeUp.mk K C L S G A R U H T P N)) ∧
      (auditTranscriptEnvelopeToEventFlow
          (AuditTranscriptEnvelopeUp.mk K C L S G A R U H T P N) ≠
        [[BMark.b0]]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact auditTranscriptEnvelopeDecode_encode_bhist
  · constructor
    · exact auditTranscriptEnvelope_round_trip _
    · intro heq
      injection heq with _ tailEq
      cases tailEq

end BEDC.Derived.AuditTranscriptEnvelopeUp
