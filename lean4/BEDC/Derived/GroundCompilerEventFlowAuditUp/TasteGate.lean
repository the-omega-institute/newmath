import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerEventFlowAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerEventFlowAuditUp : Type where
  | mk (source eventFlow channel lossless separation recognizer certificateGate transport route
      provenance nameCert : BHist) : GroundCompilerEventFlowAuditUp
  deriving DecidableEq

def groundCompilerEventFlowAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerEventFlowAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerEventFlowAuditEncodeBHist h

def groundCompilerEventFlowAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerEventFlowAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerEventFlowAuditDecodeBHist tail)

private theorem groundCompilerEventFlowAuditDecode_encode_bhist :
    ∀ h : BHist,
      groundCompilerEventFlowAuditDecodeBHist
        (groundCompilerEventFlowAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerEventFlowAuditToEventFlow : GroundCompilerEventFlowAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerEventFlowAuditUp.mk source eventFlow channel lossless separation recognizer
      certificateGate transport route provenance nameCert =>
      [[BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist source,
        [BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist eventFlow,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist channel,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist lossless,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist separation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist recognizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist certificateGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerEventFlowAuditEncodeBHist nameCert]

def groundCompilerEventFlowAuditFromEventFlow : EventFlow → Option GroundCompilerEventFlowAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | eventFlow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | channel :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | lossless :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | separation :: rest9 =>
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
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | nameCert ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (GroundCompilerEventFlowAuditUp.mk
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    source)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    eventFlow)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    channel)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    lossless)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    separation)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    recognizer)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    certificateGate)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    transport)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    route)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    provenance)
                                                                                                  (groundCompilerEventFlowAuditDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem groundCompilerEventFlowAudit_round_trip :
    ∀ x : GroundCompilerEventFlowAuditUp,
      groundCompilerEventFlowAuditFromEventFlow
        (groundCompilerEventFlowAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source eventFlow channel lossless separation recognizer certificateGate transport route
      provenance nameCert =>
      change
        some
          (GroundCompilerEventFlowAuditUp.mk
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist source))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist eventFlow))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist channel))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist lossless))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist separation))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist recognizer))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist certificateGate))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist transport))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist route))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist provenance))
            (groundCompilerEventFlowAuditDecodeBHist
              (groundCompilerEventFlowAuditEncodeBHist nameCert))) =
          some
            (GroundCompilerEventFlowAuditUp.mk source eventFlow channel lossless separation
              recognizer certificateGate transport route provenance nameCert)
      rw [groundCompilerEventFlowAuditDecode_encode_bhist source,
        groundCompilerEventFlowAuditDecode_encode_bhist eventFlow,
        groundCompilerEventFlowAuditDecode_encode_bhist channel,
        groundCompilerEventFlowAuditDecode_encode_bhist lossless,
        groundCompilerEventFlowAuditDecode_encode_bhist separation,
        groundCompilerEventFlowAuditDecode_encode_bhist recognizer,
        groundCompilerEventFlowAuditDecode_encode_bhist certificateGate,
        groundCompilerEventFlowAuditDecode_encode_bhist transport,
        groundCompilerEventFlowAuditDecode_encode_bhist route,
        groundCompilerEventFlowAuditDecode_encode_bhist provenance,
        groundCompilerEventFlowAuditDecode_encode_bhist nameCert]

private theorem groundCompilerEventFlowAuditToEventFlow_injective
    {x y : GroundCompilerEventFlowAuditUp} :
    groundCompilerEventFlowAuditToEventFlow x = groundCompilerEventFlowAuditToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerEventFlowAuditFromEventFlow (groundCompilerEventFlowAuditToEventFlow x) =
        groundCompilerEventFlowAuditFromEventFlow (groundCompilerEventFlowAuditToEventFlow y) :=
    congrArg groundCompilerEventFlowAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerEventFlowAudit_round_trip x).symm
      (Eq.trans hread (groundCompilerEventFlowAudit_round_trip y)))

instance groundCompilerEventFlowAuditBHistCarrier :
    BHistCarrier GroundCompilerEventFlowAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerEventFlowAuditToEventFlow
  fromEventFlow := groundCompilerEventFlowAuditFromEventFlow

instance groundCompilerEventFlowAuditChapterTasteGate :
    ChapterTasteGate GroundCompilerEventFlowAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerEventFlowAuditFromEventFlow
        (groundCompilerEventFlowAuditToEventFlow x) = some x
    exact groundCompilerEventFlowAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerEventFlowAuditToEventFlow_injective heq)

instance groundCompilerEventFlowAuditFieldFaithful :
    FieldFaithful GroundCompilerEventFlowAuditUp where
  fields := fun x =>
    match x with
    | GroundCompilerEventFlowAuditUp.mk source eventFlow channel lossless separation
        recognizer certificateGate transport route provenance nameCert =>
        [source, eventFlow, channel, lossless, separation, recognizer, certificateGate,
          transport, route, provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk source₁ eventFlow₁ channel₁ lossless₁ separation₁ recognizer₁ certificateGate₁
        transport₁ route₁ provenance₁ nameCert₁ =>
        cases y with
        | mk source₂ eventFlow₂ channel₂ lossless₂ separation₂ recognizer₂ certificateGate₂
            transport₂ route₂ provenance₂ nameCert₂ =>
            injection h with hSource hTail₁
            injection hTail₁ with hEventFlow hTail₂
            injection hTail₂ with hChannel hTail₃
            injection hTail₃ with hLossless hTail₄
            injection hTail₄ with hSeparation hTail₅
            injection hTail₅ with hRecognizer hTail₆
            injection hTail₆ with hCertificateGate hTail₇
            injection hTail₇ with hTransport hTail₈
            injection hTail₈ with hRoute hTail₉
            injection hTail₉ with hProvenance hTail₁₀
            injection hTail₁₀ with hNameCert _
            subst hSource
            subst hEventFlow
            subst hChannel
            subst hLossless
            subst hSeparation
            subst hRecognizer
            subst hCertificateGate
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hNameCert
            rfl

def taste_gate : ChapterTasteGate GroundCompilerEventFlowAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerEventFlowAuditChapterTasteGate

theorem GroundCompilerEventFlowAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      groundCompilerEventFlowAuditDecodeBHist
        (groundCompilerEventFlowAuditEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerEventFlowAuditUp,
        groundCompilerEventFlowAuditFromEventFlow
          (groundCompilerEventFlowAuditToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerEventFlowAuditUp,
          groundCompilerEventFlowAuditToEventFlow x =
            groundCompilerEventFlowAuditToEventFlow y -> x = y) ∧
          groundCompilerEventFlowAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerEventFlowAuditDecode_encode_bhist
  · constructor
    · exact groundCompilerEventFlowAudit_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerEventFlowAuditToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerEventFlowAuditUp
