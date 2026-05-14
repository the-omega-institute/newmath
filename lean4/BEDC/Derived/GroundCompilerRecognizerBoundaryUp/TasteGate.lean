import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerRecognizerBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerRecognizerBoundaryUp : Type where
  | mk :
      (eventFlow sourceChannel recognizer certificateGate metricReport motifReport
        bootstrapEvidence transport continuation provenance nameCert : BHist) →
      GroundCompilerRecognizerBoundaryUp
  deriving DecidableEq

def groundCompilerRecognizerBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerRecognizerBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerRecognizerBoundaryEncodeBHist h

def groundCompilerRecognizerBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerRecognizerBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerRecognizerBoundaryDecodeBHist tail)

private theorem groundCompilerRecognizerBoundary_decode_encode_bhist :
    ∀ h : BHist,
      groundCompilerRecognizerBoundaryDecodeBHist
        (groundCompilerRecognizerBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def groundCompilerRecognizerBoundaryToEventFlow :
    GroundCompilerRecognizerBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer certificateGate
      metricReport motifReport bootstrapEvidence transport continuation provenance nameCert =>
      [[BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist eventFlow,
        [BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist sourceChannel,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist recognizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist certificateGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist metricReport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist motifReport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist bootstrapEvidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerBoundaryEncodeBHist nameCert]

def groundCompilerRecognizerBoundaryFromEventFlow :
    EventFlow → Option GroundCompilerRecognizerBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | eventFlow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceChannel :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recognizer :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | certificateGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | metricReport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | motifReport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | bootstrapEvidence :: rest13 =>
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
                                                                      | continuation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (GroundCompilerRecognizerBoundaryUp.mk
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    eventFlow)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    sourceChannel)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    recognizer)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    certificateGate)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    metricReport)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    motifReport)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    bootstrapEvidence)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    transport)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    continuation)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    provenance)
                                                                                                  (groundCompilerRecognizerBoundaryDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none

private theorem groundCompilerRecognizerBoundary_round_trip :
    ∀ x : GroundCompilerRecognizerBoundaryUp,
      groundCompilerRecognizerBoundaryFromEventFlow
          (groundCompilerRecognizerBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eventFlow sourceChannel recognizer certificateGate metricReport motifReport
      bootstrapEvidence transport continuation provenance nameCert =>
      change
        some
          (GroundCompilerRecognizerBoundaryUp.mk
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist eventFlow))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist sourceChannel))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist recognizer))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist certificateGate))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist metricReport))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist motifReport))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist bootstrapEvidence))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist transport))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist continuation))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist provenance))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist nameCert))) =
          some
            (GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer
              certificateGate metricReport motifReport bootstrapEvidence transport continuation
              provenance nameCert)
      rw [groundCompilerRecognizerBoundary_decode_encode_bhist eventFlow,
        groundCompilerRecognizerBoundary_decode_encode_bhist sourceChannel,
        groundCompilerRecognizerBoundary_decode_encode_bhist recognizer,
        groundCompilerRecognizerBoundary_decode_encode_bhist certificateGate,
        groundCompilerRecognizerBoundary_decode_encode_bhist metricReport,
        groundCompilerRecognizerBoundary_decode_encode_bhist motifReport,
        groundCompilerRecognizerBoundary_decode_encode_bhist bootstrapEvidence,
        groundCompilerRecognizerBoundary_decode_encode_bhist transport,
        groundCompilerRecognizerBoundary_decode_encode_bhist continuation,
        groundCompilerRecognizerBoundary_decode_encode_bhist provenance,
        groundCompilerRecognizerBoundary_decode_encode_bhist nameCert]

private theorem groundCompilerRecognizerBoundaryToEventFlow_injective
    {x y : GroundCompilerRecognizerBoundaryUp} :
    groundCompilerRecognizerBoundaryToEventFlow x =
      groundCompilerRecognizerBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerRecognizerBoundaryFromEventFlow
          (groundCompilerRecognizerBoundaryToEventFlow x) =
        groundCompilerRecognizerBoundaryFromEventFlow
          (groundCompilerRecognizerBoundaryToEventFlow y) :=
    congrArg groundCompilerRecognizerBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerRecognizerBoundary_round_trip x).symm
      (Eq.trans hread (groundCompilerRecognizerBoundary_round_trip y)))

instance groundCompilerRecognizerBoundaryBHistCarrier :
    BHistCarrier GroundCompilerRecognizerBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerRecognizerBoundaryToEventFlow
  fromEventFlow := groundCompilerRecognizerBoundaryFromEventFlow

instance groundCompilerRecognizerBoundaryChapterTasteGate :
    ChapterTasteGate GroundCompilerRecognizerBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerRecognizerBoundaryFromEventFlow
          (groundCompilerRecognizerBoundaryToEventFlow x) = some x
    exact groundCompilerRecognizerBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerRecognizerBoundaryToEventFlow_injective heq)

instance groundCompilerRecognizerBoundaryFieldFaithful :
    FieldFaithful GroundCompilerRecognizerBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer
        certificateGate metricReport motifReport bootstrapEvidence transport continuation
        provenance nameCert =>
        [eventFlow, sourceChannel, recognizer, certificateGate, metricReport, motifReport,
          bootstrapEvidence, transport, continuation, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk eventFlow₁ sourceChannel₁ recognizer₁ certificateGate₁ metricReport₁ motifReport₁
        bootstrapEvidence₁ transport₁ continuation₁ provenance₁ nameCert₁ =>
        cases y with
        | mk eventFlow₂ sourceChannel₂ recognizer₂ certificateGate₂ metricReport₂
            motifReport₂ bootstrapEvidence₂ transport₂ continuation₂ provenance₂ nameCert₂ =>
            simp only [] at h
            injection h with hEventFlow hRest₁
            injection hRest₁ with hSourceChannel hRest₂
            injection hRest₂ with hRecognizer hRest₃
            injection hRest₃ with hCertificateGate hRest₄
            injection hRest₄ with hMetricReport hRest₅
            injection hRest₅ with hMotifReport hRest₆
            injection hRest₆ with hBootstrapEvidence hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hContinuation hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hNameCert _
            subst hEventFlow
            subst hSourceChannel
            subst hRecognizer
            subst hCertificateGate
            subst hMetricReport
            subst hMotifReport
            subst hBootstrapEvidence
            subst hTransport
            subst hContinuation
            subst hProvenance
            subst hNameCert
            rfl

theorem GroundCompilerRecognizerBoundaryUpTasteGate_single_carrier_alignment :
    (∀ x : GroundCompilerRecognizerBoundaryUp, ∃ e : EventFlow,
      BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : GroundCompilerRecognizerBoundaryUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) → List.Mem m w →
          m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact ⟨groundCompilerRecognizerBoundaryToEventFlow x,
      groundCompilerRecognizerBoundary_round_trip x⟩
  · intro x w m hw hm
    exact BEDC.GroundCompiler.EventFlow.event_flow_conservativity
      (S := BHistCarrier.toEventFlow x) hw hm

end BEDC.Derived.GroundCompilerRecognizerBoundaryUp
