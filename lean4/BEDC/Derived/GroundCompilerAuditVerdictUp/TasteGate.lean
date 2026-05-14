import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerAuditVerdictUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerAuditVerdictUp : Type where
  | mk
      (moduleRow queryOutput forbidden verdict alignment recognizer certificateGate boundary
        transport replay provenance nameCert : BHist) :
      GroundCompilerAuditVerdictUp
  deriving DecidableEq

def groundCompilerAuditVerdictEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerAuditVerdictEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerAuditVerdictEncodeBHist h

def groundCompilerAuditVerdictDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerAuditVerdictDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerAuditVerdictDecodeBHist tail)

private theorem groundCompilerAuditVerdict_decode_encode_bhist :
    ∀ h : BHist,
      groundCompilerAuditVerdictDecodeBHist
        (groundCompilerAuditVerdictEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerAuditVerdictToEventFlow :
    GroundCompilerAuditVerdictUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerAuditVerdictUp.mk moduleRow queryOutput forbidden verdict alignment
      recognizer certificateGate boundary transport replay provenance nameCert =>
      [[BMark.b0],
        groundCompilerAuditVerdictEncodeBHist moduleRow,
        [BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist queryOutput,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist forbidden,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist verdict,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist alignment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist recognizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist certificateGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundCompilerAuditVerdictEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditVerdictEncodeBHist nameCert]

def groundCompilerAuditVerdictFromEventFlow :
    EventFlow → Option GroundCompilerAuditVerdictUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | moduleRow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | queryOutput :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | forbidden :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | verdict :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | alignment :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | recognizer :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | certificateGate :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | boundary :: rest15 =>
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
                                                                                                        (GroundCompilerAuditVerdictUp.mk
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            moduleRow)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            queryOutput)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            forbidden)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            verdict)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            alignment)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            recognizer)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            certificateGate)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            boundary)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            transport)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            replay)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            provenance)
                                                                                                          (groundCompilerAuditVerdictDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem groundCompilerAuditVerdict_round_trip :
    ∀ x : GroundCompilerAuditVerdictUp,
      groundCompilerAuditVerdictFromEventFlow
        (groundCompilerAuditVerdictToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk moduleRow queryOutput forbidden verdict alignment recognizer certificateGate
      boundary transport replay provenance nameCert =>
      change
        some
          (GroundCompilerAuditVerdictUp.mk
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist moduleRow))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist queryOutput))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist forbidden))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist verdict))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist alignment))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist recognizer))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist certificateGate))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist boundary))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist transport))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist replay))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist provenance))
            (groundCompilerAuditVerdictDecodeBHist
              (groundCompilerAuditVerdictEncodeBHist nameCert))) =
          some
            (GroundCompilerAuditVerdictUp.mk moduleRow queryOutput forbidden verdict
              alignment recognizer certificateGate boundary transport replay provenance
              nameCert)
      rw [groundCompilerAuditVerdict_decode_encode_bhist moduleRow,
        groundCompilerAuditVerdict_decode_encode_bhist queryOutput,
        groundCompilerAuditVerdict_decode_encode_bhist forbidden,
        groundCompilerAuditVerdict_decode_encode_bhist verdict,
        groundCompilerAuditVerdict_decode_encode_bhist alignment,
        groundCompilerAuditVerdict_decode_encode_bhist recognizer,
        groundCompilerAuditVerdict_decode_encode_bhist certificateGate,
        groundCompilerAuditVerdict_decode_encode_bhist boundary,
        groundCompilerAuditVerdict_decode_encode_bhist transport,
        groundCompilerAuditVerdict_decode_encode_bhist replay,
        groundCompilerAuditVerdict_decode_encode_bhist provenance,
        groundCompilerAuditVerdict_decode_encode_bhist nameCert]

private theorem groundCompilerAuditVerdictToEventFlow_injective
    {x y : GroundCompilerAuditVerdictUp} :
    groundCompilerAuditVerdictToEventFlow x =
      groundCompilerAuditVerdictToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerAuditVerdictFromEventFlow
          (groundCompilerAuditVerdictToEventFlow x) =
        groundCompilerAuditVerdictFromEventFlow
          (groundCompilerAuditVerdictToEventFlow y) :=
    congrArg groundCompilerAuditVerdictFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerAuditVerdict_round_trip x).symm
      (Eq.trans hread (groundCompilerAuditVerdict_round_trip y)))

instance groundCompilerAuditVerdictBHistCarrier :
    BHistCarrier GroundCompilerAuditVerdictUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerAuditVerdictToEventFlow
  fromEventFlow := groundCompilerAuditVerdictFromEventFlow

instance groundCompilerAuditVerdictChapterTasteGate :
    ChapterTasteGate GroundCompilerAuditVerdictUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerAuditVerdictFromEventFlow
        (groundCompilerAuditVerdictToEventFlow x) = some x
    exact groundCompilerAuditVerdict_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerAuditVerdictToEventFlow_injective heq)

instance groundCompilerAuditVerdictFieldFaithful :
    FieldFaithful GroundCompilerAuditVerdictUp where
  fields := fun x =>
    match x with
    | GroundCompilerAuditVerdictUp.mk moduleRow queryOutput forbidden verdict alignment
        recognizer certificateGate boundary transport replay provenance nameCert =>
        [moduleRow, queryOutput, forbidden, verdict, alignment, recognizer,
          certificateGate, boundary, transport, replay, provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk moduleRow₁ queryOutput₁ forbidden₁ verdict₁ alignment₁ recognizer₁
        certificateGate₁ boundary₁ transport₁ replay₁ provenance₁ nameCert₁ =>
        cases y with
        | mk moduleRow₂ queryOutput₂ forbidden₂ verdict₂ alignment₂ recognizer₂
            certificateGate₂ boundary₂ transport₂ replay₂ provenance₂ nameCert₂ =>
            injection h with hModuleRow hTail₁
            injection hTail₁ with hQueryOutput hTail₂
            injection hTail₂ with hForbidden hTail₃
            injection hTail₃ with hVerdict hTail₄
            injection hTail₄ with hAlignment hTail₅
            injection hTail₅ with hRecognizer hTail₆
            injection hTail₆ with hCertificateGate hTail₇
            injection hTail₇ with hBoundary hTail₈
            injection hTail₈ with hTransport hTail₉
            injection hTail₉ with hReplay hTail₁₀
            injection hTail₁₀ with hProvenance hTail₁₁
            injection hTail₁₁ with hNameCert _
            subst hModuleRow
            subst hQueryOutput
            subst hForbidden
            subst hVerdict
            subst hAlignment
            subst hRecognizer
            subst hCertificateGate
            subst hBoundary
            subst hTransport
            subst hReplay
            subst hProvenance
            subst hNameCert
            rfl

def taste_gate : ChapterTasteGate GroundCompilerAuditVerdictUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerAuditVerdictChapterTasteGate

theorem GroundCompilerAuditVerdictTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      groundCompilerAuditVerdictDecodeBHist
        (groundCompilerAuditVerdictEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerAuditVerdictUp,
        groundCompilerAuditVerdictFromEventFlow
          (groundCompilerAuditVerdictToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerAuditVerdictUp,
          groundCompilerAuditVerdictToEventFlow x =
            groundCompilerAuditVerdictToEventFlow y → x = y) ∧
          groundCompilerAuditVerdictEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerAuditVerdict_decode_encode_bhist
  · constructor
    · exact groundCompilerAuditVerdict_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerAuditVerdictToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerAuditVerdictUp
