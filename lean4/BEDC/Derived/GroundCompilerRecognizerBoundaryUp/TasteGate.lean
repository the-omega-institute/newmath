import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerRecognizerBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerRecognizerBoundaryUp : Type where
  | mk
      (eventFlow sourceChannel recognizer certificateGate metricReport motifReport
        bootstrapEvidence transports routes provenance localName : BHist) :
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

private theorem groundCompilerRecognizerBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      groundCompilerRecognizerBoundaryDecodeBHist
        (groundCompilerRecognizerBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem groundCompilerRecognizerBoundary_mk_congr
    {eventFlow eventFlow' sourceChannel sourceChannel' recognizer recognizer'
      certificateGate certificateGate' metricReport metricReport' motifReport motifReport'
      bootstrapEvidence bootstrapEvidence' transports transports' routes routes'
      provenance provenance' localName localName' : BHist}
    (hEventFlow : eventFlow' = eventFlow)
    (hSourceChannel : sourceChannel' = sourceChannel)
    (hRecognizer : recognizer' = recognizer)
    (hCertificateGate : certificateGate' = certificateGate)
    (hMetricReport : metricReport' = metricReport)
    (hMotifReport : motifReport' = motifReport)
    (hBootstrapEvidence : bootstrapEvidence' = bootstrapEvidence)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    GroundCompilerRecognizerBoundaryUp.mk eventFlow' sourceChannel' recognizer'
        certificateGate' metricReport' motifReport' bootstrapEvidence' transports' routes'
        provenance' localName' =
      GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer certificateGate
        metricReport motifReport bootstrapEvidence transports routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEventFlow
  cases hSourceChannel
  cases hRecognizer
  cases hCertificateGate
  cases hMetricReport
  cases hMotifReport
  cases hBootstrapEvidence
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

def groundCompilerRecognizerBoundaryToEventFlow :
    GroundCompilerRecognizerBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer certificateGate
      metricReport motifReport bootstrapEvidence transports routes provenance localName =>
      [groundCompilerRecognizerBoundaryEncodeBHist eventFlow,
        groundCompilerRecognizerBoundaryEncodeBHist sourceChannel,
        groundCompilerRecognizerBoundaryEncodeBHist recognizer,
        groundCompilerRecognizerBoundaryEncodeBHist certificateGate,
        groundCompilerRecognizerBoundaryEncodeBHist metricReport,
        groundCompilerRecognizerBoundaryEncodeBHist motifReport,
        groundCompilerRecognizerBoundaryEncodeBHist bootstrapEvidence,
        groundCompilerRecognizerBoundaryEncodeBHist transports,
        groundCompilerRecognizerBoundaryEncodeBHist routes,
        groundCompilerRecognizerBoundaryEncodeBHist provenance,
        groundCompilerRecognizerBoundaryEncodeBHist localName]

def groundCompilerRecognizerBoundaryFromEventFlow :
    EventFlow → Option GroundCompilerRecognizerBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | eventFlow :: rest0 =>
      match rest0 with
      | [] => none
      | sourceChannel :: rest1 =>
          match rest1 with
          | [] => none
          | recognizer :: rest2 =>
              match rest2 with
              | [] => none
              | certificateGate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | metricReport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | motifReport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | bootstrapEvidence :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transports :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | routes :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
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
                                                        transports)
                                                      (groundCompilerRecognizerBoundaryDecodeBHist
                                                        routes)
                                                      (groundCompilerRecognizerBoundaryDecodeBHist
                                                        provenance)
                                                      (groundCompilerRecognizerBoundaryDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem groundCompilerRecognizerBoundary_round_trip :
    ∀ x : GroundCompilerRecognizerBoundaryUp,
      groundCompilerRecognizerBoundaryFromEventFlow
        (groundCompilerRecognizerBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eventFlow sourceChannel recognizer certificateGate metricReport motifReport
      bootstrapEvidence transports routes provenance localName =>
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
              (groundCompilerRecognizerBoundaryEncodeBHist transports))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist routes))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist provenance))
            (groundCompilerRecognizerBoundaryDecodeBHist
              (groundCompilerRecognizerBoundaryEncodeBHist localName))) =
          some
            (GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer
              certificateGate metricReport motifReport bootstrapEvidence transports routes
              provenance localName)
      exact
        congrArg some
          (groundCompilerRecognizerBoundary_mk_congr
            (groundCompilerRecognizerBoundaryDecode_encode_bhist eventFlow)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist sourceChannel)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist recognizer)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist certificateGate)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist metricReport)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist motifReport)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist bootstrapEvidence)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist transports)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist routes)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist provenance)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist localName))

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
    | GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer certificateGate
        metricReport motifReport bootstrapEvidence transports routes provenance localName =>
        [eventFlow, sourceChannel, recognizer, certificateGate, metricReport, motifReport,
          bootstrapEvidence, transports, routes, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk eventFlow₁ sourceChannel₁ recognizer₁ certificateGate₁ metricReport₁ motifReport₁
        bootstrapEvidence₁ transports₁ routes₁ provenance₁ localName₁ =>
        cases y with
        | mk eventFlow₂ sourceChannel₂ recognizer₂ certificateGate₂ metricReport₂ motifReport₂
            bootstrapEvidence₂ transports₂ routes₂ provenance₂ localName₂ =>
            injection h with hEventFlow t1
            injection t1 with hSourceChannel t2
            injection t2 with hRecognizer t3
            injection t3 with hCertificateGate t4
            injection t4 with hMetricReport t5
            injection t5 with hMotifReport t6
            injection t6 with hBootstrapEvidence t7
            injection t7 with hTransports t8
            injection t8 with hRoutes t9
            injection t9 with hProvenance t10
            injection t10 with hLocalName _
            cases hEventFlow
            cases hSourceChannel
            cases hRecognizer
            cases hCertificateGate
            cases hMetricReport
            cases hMotifReport
            cases hBootstrapEvidence
            cases hTransports
            cases hRoutes
            cases hProvenance
            cases hLocalName
            rfl

theorem GroundCompilerRecognizerBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      groundCompilerRecognizerBoundaryDecodeBHist
        (groundCompilerRecognizerBoundaryEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerRecognizerBoundaryUp,
        groundCompilerRecognizerBoundaryFromEventFlow
          (groundCompilerRecognizerBoundaryToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerRecognizerBoundaryUp,
          groundCompilerRecognizerBoundaryToEventFlow x =
            groundCompilerRecognizerBoundaryToEventFlow y → x = y) ∧
          groundCompilerRecognizerBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerRecognizerBoundaryDecode_encode_bhist
  · constructor
    · exact groundCompilerRecognizerBoundary_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerRecognizerBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerRecognizerBoundaryUp
