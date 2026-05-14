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
        bootstrapEvidence transport continuation provenance localName : BHist) →
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
          (groundCompilerRecognizerBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem groundCompilerRecognizerBoundary_mk_congr
    {eventFlow eventFlow' sourceChannel sourceChannel' recognizer recognizer'
      certificateGate certificateGate' metricReport metricReport' motifReport motifReport'
      bootstrapEvidence bootstrapEvidence' transport transport' continuation continuation'
      provenance provenance' localName localName' : BHist}
    (hEventFlow : eventFlow' = eventFlow)
    (hSourceChannel : sourceChannel' = sourceChannel)
    (hRecognizer : recognizer' = recognizer)
    (hCertificateGate : certificateGate' = certificateGate)
    (hMetricReport : metricReport' = metricReport)
    (hMotifReport : motifReport' = motifReport)
    (hBootstrapEvidence : bootstrapEvidence' = bootstrapEvidence)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    GroundCompilerRecognizerBoundaryUp.mk eventFlow' sourceChannel' recognizer'
        certificateGate' metricReport' motifReport' bootstrapEvidence' transport'
        continuation' provenance' localName' =
      GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer
        certificateGate metricReport motifReport bootstrapEvidence transport continuation
        provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEventFlow
  cases hSourceChannel
  cases hRecognizer
  cases hCertificateGate
  cases hMetricReport
  cases hMotifReport
  cases hBootstrapEvidence
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

def groundCompilerRecognizerBoundaryToEventFlow :
    GroundCompilerRecognizerBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer
      certificateGate metricReport motifReport bootstrapEvidence transport continuation
      provenance localName =>
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
        groundCompilerRecognizerBoundaryEncodeBHist localName]

def groundCompilerRecognizerBoundaryFromEventFlow :
    EventFlow → Option GroundCompilerRecognizerBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: eventFlow :: _tag1 :: sourceChannel :: _tag2 :: recognizer ::
      _tag3 :: certificateGate :: _tag4 :: metricReport :: _tag5 :: motifReport ::
      _tag6 :: bootstrapEvidence :: _tag7 :: transport :: _tag8 :: continuation ::
      _tag9 :: provenance :: _tag10 :: localName :: [] =>
      some
        (GroundCompilerRecognizerBoundaryUp.mk
          (groundCompilerRecognizerBoundaryDecodeBHist eventFlow)
          (groundCompilerRecognizerBoundaryDecodeBHist sourceChannel)
          (groundCompilerRecognizerBoundaryDecodeBHist recognizer)
          (groundCompilerRecognizerBoundaryDecodeBHist certificateGate)
          (groundCompilerRecognizerBoundaryDecodeBHist metricReport)
          (groundCompilerRecognizerBoundaryDecodeBHist motifReport)
          (groundCompilerRecognizerBoundaryDecodeBHist bootstrapEvidence)
          (groundCompilerRecognizerBoundaryDecodeBHist transport)
          (groundCompilerRecognizerBoundaryDecodeBHist continuation)
          (groundCompilerRecognizerBoundaryDecodeBHist provenance)
          (groundCompilerRecognizerBoundaryDecodeBHist localName))
  | _ => none

private theorem groundCompilerRecognizerBoundary_round_trip :
    ∀ x : GroundCompilerRecognizerBoundaryUp,
      groundCompilerRecognizerBoundaryFromEventFlow
          (groundCompilerRecognizerBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eventFlow sourceChannel recognizer certificateGate metricReport motifReport
      bootstrapEvidence transport continuation provenance localName =>
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
              (groundCompilerRecognizerBoundaryEncodeBHist localName))) =
          some
            (GroundCompilerRecognizerBoundaryUp.mk eventFlow sourceChannel recognizer
              certificateGate metricReport motifReport bootstrapEvidence transport
              continuation provenance localName)
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
            (groundCompilerRecognizerBoundaryDecode_encode_bhist transport)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist continuation)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist provenance)
            (groundCompilerRecognizerBoundaryDecode_encode_bhist localName))

private theorem groundCompilerRecognizerBoundaryToEventFlow_injective
    {x y : GroundCompilerRecognizerBoundaryUp} :
    groundCompilerRecognizerBoundaryToEventFlow x =
        groundCompilerRecognizerBoundaryToEventFlow y →
      x = y := by
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
    change groundCompilerRecognizerBoundaryFromEventFlow
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
        provenance localName =>
        [eventFlow, sourceChannel, recognizer, certificateGate, metricReport, motifReport,
          bootstrapEvidence, transport, continuation, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk eventFlow1 sourceChannel1 recognizer1 certificateGate1 metricReport1 motifReport1
        bootstrapEvidence1 transport1 continuation1 provenance1 localName1 =>
        cases y with
        | mk eventFlow2 sourceChannel2 recognizer2 certificateGate2 metricReport2 motifReport2
            bootstrapEvidence2 transport2 continuation2 provenance2 localName2 =>
            injection h with hEventFlow t1
            injection t1 with hSourceChannel t2
            injection t2 with hRecognizer t3
            injection t3 with hCertificateGate t4
            injection t4 with hMetricReport t5
            injection t5 with hMotifReport t6
            injection t6 with hBootstrapEvidence t7
            injection t7 with hTransport t8
            injection t8 with hContinuation t9
            injection t9 with hProvenance t10
            injection t10 with hLocalName _
            cases hEventFlow
            cases hSourceChannel
            cases hRecognizer
            cases hCertificateGate
            cases hMetricReport
            cases hMotifReport
            cases hBootstrapEvidence
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hLocalName
            rfl

end BEDC.Derived.GroundCompilerRecognizerBoundaryUp
