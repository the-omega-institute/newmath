import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WritingItemAuditPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WritingItemAuditPacketUp : Type where
  | mk :
      (kind carrier classifier ledger theoryStatus formalStatus gapReport permittedClaim
        transport replay provenance localName : BHist) →
      WritingItemAuditPacketUp
  deriving DecidableEq

private def writingItemAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: writingItemAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: writingItemAuditPacketEncodeBHist h

private def writingItemAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (writingItemAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (writingItemAuditPacketDecodeBHist tail)

private theorem writingItemAuditPacketDecode_encode_bhist :
    ∀ h : BHist,
      writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem writingItemAuditPacket_mk_congr
    {kind kind' carrier carrier' classifier classifier' ledger ledger'
      theoryStatus theoryStatus' formalStatus formalStatus' gapReport gapReport'
      permittedClaim permittedClaim' transport transport' replay replay'
      provenance provenance' localName localName' : BHist}
    (hKind : kind' = kind)
    (hCarrier : carrier' = carrier)
    (hClassifier : classifier' = classifier)
    (hLedger : ledger' = ledger)
    (hTheoryStatus : theoryStatus' = theoryStatus)
    (hFormalStatus : formalStatus' = formalStatus)
    (hGapReport : gapReport' = gapReport)
    (hPermittedClaim : permittedClaim' = permittedClaim)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    WritingItemAuditPacketUp.mk kind' carrier' classifier' ledger' theoryStatus'
        formalStatus' gapReport' permittedClaim' transport' replay' provenance' localName' =
      WritingItemAuditPacketUp.mk kind carrier classifier ledger theoryStatus formalStatus
        gapReport permittedClaim transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hKind
  cases hCarrier
  cases hClassifier
  cases hLedger
  cases hTheoryStatus
  cases hFormalStatus
  cases hGapReport
  cases hPermittedClaim
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

private def writingItemAuditPacketToEventFlow : WritingItemAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WritingItemAuditPacketUp.mk kind carrier classifier ledger theoryStatus formalStatus
      gapReport permittedClaim transport replay provenance localName =>
      [[BMark.b0],
        writingItemAuditPacketEncodeBHist kind,
        [BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist carrier,
        [BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist theoryStatus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist formalStatus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist gapReport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        writingItemAuditPacketEncodeBHist permittedClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist localName]

private def writingItemAuditPacketFromEventFlow :
    EventFlow → Option WritingItemAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | kind :: rest1 =>
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
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | theoryStatus :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | formalStatus :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | gapReport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | permittedClaim :: rest15 =>
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
                                                                              | replay :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | localName :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (WritingItemAuditPacketUp.mk
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            kind)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            carrier)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            classifier)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            ledger)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            theoryStatus)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            formalStatus)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            gapReport)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            permittedClaim)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            transport)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            replay)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            provenance)
                                                                                                          (writingItemAuditPacketDecodeBHist
                                                                                                            localName))
                                                                                                  | _ :: _ => none

private theorem writingItemAuditPacket_round_trip :
    ∀ x : WritingItemAuditPacketUp,
      writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk kind carrier classifier ledger theoryStatus formalStatus gapReport permittedClaim
      transport replay provenance localName =>
      change
        some
          (WritingItemAuditPacketUp.mk
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist kind))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist carrier))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist classifier))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist ledger))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist theoryStatus))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist formalStatus))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist gapReport))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist permittedClaim))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist transport))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist replay))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist provenance))
            (writingItemAuditPacketDecodeBHist
              (writingItemAuditPacketEncodeBHist localName))) =
          some
            (WritingItemAuditPacketUp.mk kind carrier classifier ledger theoryStatus
              formalStatus gapReport permittedClaim transport replay provenance localName)
      exact
        congrArg some
          (writingItemAuditPacket_mk_congr
            (writingItemAuditPacketDecode_encode_bhist kind)
            (writingItemAuditPacketDecode_encode_bhist carrier)
            (writingItemAuditPacketDecode_encode_bhist classifier)
            (writingItemAuditPacketDecode_encode_bhist ledger)
            (writingItemAuditPacketDecode_encode_bhist theoryStatus)
            (writingItemAuditPacketDecode_encode_bhist formalStatus)
            (writingItemAuditPacketDecode_encode_bhist gapReport)
            (writingItemAuditPacketDecode_encode_bhist permittedClaim)
            (writingItemAuditPacketDecode_encode_bhist transport)
            (writingItemAuditPacketDecode_encode_bhist replay)
            (writingItemAuditPacketDecode_encode_bhist provenance)
            (writingItemAuditPacketDecode_encode_bhist localName))

private theorem writingItemAuditPacketToEventFlow_injective
    {x y : WritingItemAuditPacketUp} :
    writingItemAuditPacketToEventFlow x = writingItemAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) =
        writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow y) :=
    congrArg writingItemAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (writingItemAuditPacket_round_trip x).symm
      (Eq.trans hread (writingItemAuditPacket_round_trip y)))

private def writingItemAuditPacketFields : WritingItemAuditPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WritingItemAuditPacketUp.mk kind carrier classifier ledger theoryStatus formalStatus
      gapReport permittedClaim transport replay provenance localName =>
      [kind, carrier, classifier, ledger, theoryStatus, formalStatus, gapReport,
        permittedClaim, transport, replay, provenance, localName]

private theorem writingItemAuditPacket_field_faithful :
    ∀ x y : WritingItemAuditPacketUp,
      writingItemAuditPacketFields x = writingItemAuditPacketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk kind₁ carrier₁ classifier₁ ledger₁ theoryStatus₁ formalStatus₁ gapReport₁
      permittedClaim₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk kind₂ carrier₂ classifier₂ ledger₂ theoryStatus₂ formalStatus₂ gapReport₂
          permittedClaim₂ transport₂ replay₂ provenance₂ localName₂ =>
          change
              [kind₁, carrier₁, classifier₁, ledger₁, theoryStatus₁, formalStatus₁,
                gapReport₁, permittedClaim₁, transport₁, replay₁, provenance₁,
                localName₁] =
                [kind₂, carrier₂, classifier₂, ledger₂, theoryStatus₂, formalStatus₂,
                  gapReport₂, permittedClaim₂, transport₂, replay₂, provenance₂,
                  localName₂] at h
          injection h with hKind t1
          injection t1 with hCarrier t2
          injection t2 with hClassifier t3
          injection t3 with hLedger t4
          injection t4 with hTheoryStatus t5
          injection t5 with hFormalStatus t6
          injection t6 with hGapReport t7
          injection t7 with hPermittedClaim t8
          injection t8 with hTransport t9
          injection t9 with hReplay t10
          injection t10 with hProvenance t11
          injection t11 with hLocalName _
          cases hKind
          cases hCarrier
          cases hClassifier
          cases hLedger
          cases hTheoryStatus
          cases hFormalStatus
          cases hGapReport
          cases hPermittedClaim
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hLocalName
          rfl

instance writingItemAuditPacketBHistCarrier :
    BHistCarrier WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := writingItemAuditPacketToEventFlow
  fromEventFlow := writingItemAuditPacketFromEventFlow

instance writingItemAuditPacketChapterTasteGate :
    ChapterTasteGate WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      writingItemAuditPacketFromEventFlow
        (writingItemAuditPacketToEventFlow x) = some x
    exact writingItemAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (writingItemAuditPacketToEventFlow_injective heq)

instance writingItemAuditPacketFieldFaithful :
    FieldFaithful WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := writingItemAuditPacketFields
  field_faithful := writingItemAuditPacket_field_faithful

instance writingItemAuditPacketNontrivial :
    Nontrivial WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WritingItemAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      WritingItemAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WritingItemAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  writingItemAuditPacketChapterTasteGate

theorem WritingItemAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist h) = h) ∧
      (∀ x : WritingItemAuditPacketUp,
        writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : WritingItemAuditPacketUp,
          writingItemAuditPacketToEventFlow x = writingItemAuditPacketToEventFlow y → x = y) ∧
          writingItemAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact writingItemAuditPacketDecode_encode_bhist
  · constructor
    · exact writingItemAuditPacket_round_trip
    · constructor
      · intro x y heq
        exact writingItemAuditPacketToEventFlow_injective heq
      · rfl

theorem WritingItemAuditPacketNameCert_obligations
    (x : WritingItemAuditPacketUp) :
    ∃ K C R L T F G Q H A P N : BHist,
      x = WritingItemAuditPacketUp.mk K C R L T F G Q H A P N ∧
        FieldFaithful.fields x = [K, C, R, L, T, F, G, Q, H, A, P, N] ∧
          hsame H H ∧ Cont A P (append A P) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K C R L T F G Q H A P N =>
      exact ⟨K, C, R, L, T, F, G, Q, H, A, P, N, rfl, rfl, hsame_refl H, rfl⟩

end BEDC.Derived.WritingItemAuditPacketUp
