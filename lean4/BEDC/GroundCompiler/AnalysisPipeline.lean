import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.SemanticMotif
import BEDC.GroundCompiler.MetricsFlow
import BEDC.GroundCompiler.HigherCaseStudies

namespace BEDC.GroundCompiler.AnalysisPipeline

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.SemanticMotif
open BEDC.GroundCompiler.MetricsFlow
open BEDC.GroundCompiler.CaseStudies

inductive AnalysisInput : Type where
  | channel (c : List DisplayAlphabet) : LegalZStream c -> AnalysisInput
  | source (S : EventFlow) : AnalysisInput

def AnalysisInputSource (input : AnalysisInput) (S : EventFlow) : Prop :=
  match input with
  | AnalysisInput.channel c _ => Decode c = some S
  | AnalysisInput.source S0 => S = S0

theorem decode_first_analysis {c : List DisplayAlphabet} :
    LegalZStream c -> exists S : EventFlow, Decode c = some S := by
  intro h
  cases legal_stream_completeness h with
  | intro S hS =>
      exact ⟨S, hS.left⟩

def AnalysisProtocolCandidateFlow : Type := EventFlow

def GeneratedAnalysisProtocolRecognizer : Type := EventFlow

def RecognizesAnalysisProtocol
    (R : GeneratedAnalysisProtocolRecognizer)
    (P : AnalysisProtocolCandidateFlow) : Prop :=
  NonemptyEventFlow R /\ NonemptyEventFlow P

def RecognizedAnalysisProtocolFlow
    (P : AnalysisProtocolCandidateFlow) : Prop :=
  exists R : GeneratedAnalysisProtocolRecognizer,
    RecognizesAnalysisProtocol R P

inductive AnalysisProtocolRole : Type where
  | inputDomain
  | recognizerFamily
  | motifSelection
  | metricSelection
  | metricWeights
  | normalizationPolicy
  | ledgerPolicy
  | cannotClaimPolicy
  | bridgeObligationPolicy
  | reportPolicy
  | seal

def EventSubflow (part whole : EventFlow) : Prop :=
  exists pre post : EventFlow, whole = List.append pre (List.append part post)

def AnalysisProtocolSubflow
    (R : GeneratedAnalysisProtocolRecognizer)
    (P part : AnalysisProtocolCandidateFlow)
    (_role : AnalysisProtocolRole) : Prop :=
  RecognizesAnalysisProtocol R P /\
    EventSubflow part P /\
    NonemptyEventFlow part

inductive AnalysisConfigDatum : Type where
  | protocolFlow (P : AnalysisProtocolCandidateFlow)
  | analysisYAML
  | metricJSON
  | motifTable
  | weightVector
  | reportTemplate
  | manualObjectGrouping
  | humanTheoryCategoryList
  | externalBridgeCandidateList

inductive ExternalAnalysisConfig : AnalysisConfigDatum -> Prop where
  | analysisYAML :
      ExternalAnalysisConfig AnalysisConfigDatum.analysisYAML
  | metricJSON :
      ExternalAnalysisConfig AnalysisConfigDatum.metricJSON
  | motifTable :
      ExternalAnalysisConfig AnalysisConfigDatum.motifTable
  | weightVector :
      ExternalAnalysisConfig AnalysisConfigDatum.weightVector
  | reportTemplate :
      ExternalAnalysisConfig AnalysisConfigDatum.reportTemplate
  | manualObjectGrouping :
      ExternalAnalysisConfig AnalysisConfigDatum.manualObjectGrouping
  | humanTheoryCategoryList :
      ExternalAnalysisConfig AnalysisConfigDatum.humanTheoryCategoryList
  | externalBridgeCandidateList :
      ExternalAnalysisConfig AnalysisConfigDatum.externalBridgeCandidateList

inductive FormalAnalysisConfig : AnalysisConfigDatum -> Prop where
  | protocol {P : AnalysisProtocolCandidateFlow} :
      RecognizedAnalysisProtocolFlow P ->
        FormalAnalysisConfig (AnalysisConfigDatum.protocolFlow P)

def MetricWeightsRecordedByProtocol
    (P weights : AnalysisProtocolCandidateFlow) : Prop :=
  exists R : GeneratedAnalysisProtocolRecognizer,
    AnalysisProtocolSubflow R P weights AnalysisProtocolRole.metricWeights

inductive FormalWeightedMetric : AnalysisProtocolCandidateFlow ->
    AnalysisProtocolCandidateFlow -> Prop where
  | protocol {P weights : AnalysisProtocolCandidateFlow} :
      MetricWeightsRecordedByProtocol P weights ->
        FormalWeightedMetric P weights

inductive AnalysisStage : Type where
  | legalityCheck
  | decode
  | protocolRecognition
  | recognizerFamilyExtraction
  | motifExtraction
  | metricComputation
  | normalAddressAnalysis
  | ledgerAudit
  | cannotClaimAudit
  | bridgeObligationDiscovery
  | reportGeneration

def AnalysisPipelineStages : List AnalysisStage :=
  [AnalysisStage.legalityCheck,
    AnalysisStage.decode,
    AnalysisStage.protocolRecognition,
    AnalysisStage.recognizerFamilyExtraction,
    AnalysisStage.motifExtraction,
    AnalysisStage.metricComputation,
    AnalysisStage.normalAddressAnalysis,
    AnalysisStage.ledgerAudit,
    AnalysisStage.cannotClaimAudit,
    AnalysisStage.bridgeObligationDiscovery,
    AnalysisStage.reportGeneration]

def Analyze
    (_c : List DisplayAlphabet)
    (_P : AnalysisProtocolCandidateFlow) : List AnalysisStage :=
  AnalysisPipelineStages

def StageLegality (c : List DisplayAlphabet) : Prop :=
  LegalZStream c

def StageDecode (c : List DisplayAlphabet) (S : EventFlow) : Prop :=
  Decode c = some S

def StageProtocol
    (R : GeneratedAnalysisProtocolRecognizer)
    (P : AnalysisProtocolCandidateFlow) : Prop :=
  RecognizesAnalysisProtocol R P

def CertifiedOrBootstrapRecognizer
    (R cert : GeneratedRecognizer) : Prop :=
  NonemptyEventFlow R /\
    FormalCompilerInput (CompilerDatum.recognizedFlow cert R)

def StageRecognizerFamilyExtraction
    (R : GeneratedAnalysisProtocolRecognizer)
    (P familyFlow : AnalysisProtocolCandidateFlow)
    (Rfam : List GeneratedRecognizer) : Prop :=
  AnalysisProtocolSubflow R P familyFlow AnalysisProtocolRole.recognizerFamily /\
    forall Ri : GeneratedRecognizer,
      List.Mem Ri Rfam ->
        exists cert : GeneratedRecognizer, CertifiedOrBootstrapRecognizer Ri cert

structure PipelineMotifEntry where
  recognizer : GeneratedMotifRecognizer
  support : EventFlow
  role : MotifRole
  ledger : EventFlow

def StageMotifExtraction
    (Rfam : List GeneratedMotifRecognizer) (S : EventFlow)
    (profile : List PipelineMotifEntry) : Prop :=
  forall entry : PipelineMotifEntry,
    List.Mem entry profile ->
      List.Mem entry.recognizer Rfam /\
        RecognizesMotif entry.recognizer S entry.support entry.role /\
        MotifLedger entry.recognizer S entry.support entry.role entry.ledger

def MetricSelectedByProtocol
    (P metricFlow : AnalysisProtocolCandidateFlow) : Prop :=
  exists R : GeneratedAnalysisProtocolRecognizer,
    AnalysisProtocolSubflow R P metricFlow AnalysisProtocolRole.metricSelection

def StageMetricComputation
    (P metricFlow : AnalysisProtocolCandidateFlow) (spec : MetricSpec) : Prop :=
  MetricSelectedByProtocol P metricFlow /\ MetricAdmissible spec

def StageNormalAddressAnalysis
    (P policyFlow : AnalysisProtocolCandidateFlow)
    (Rfam : MetricRecognizerFamily) (S : EventFlow)
    (records : List NormalAddressRecord) : Prop :=
  (exists R : GeneratedAnalysisProtocolRecognizer,
    AnalysisProtocolSubflow R P policyFlow
      AnalysisProtocolRole.normalizationPolicy) /\
    NormalAddressMap Rfam S records

inductive LedgerAuditFailureKind : Type where
  | motifWithoutLedger
  | packageWithoutLedger
  | nameCertWithoutLedger
  | completionWithoutTailLedger
  | carryWithoutPreNormalLedger
  | bridgeWithoutNoHostLeakLedger

structure LedgerAuditFailureItem where
  kind : LedgerAuditFailureKind
  support : EventFlow

def StageLedgerAudit
    (profile : List PipelineMotifEntry)
    (failures : List LedgerAuditFailureItem) : Prop :=
  forall entry : PipelineMotifEntry,
    List.Mem entry profile ->
      NonemptyEventFlow entry.ledger \/
        exists failure : LedgerAuditFailureItem,
          List.Mem failure failures /\
            failure.kind = LedgerAuditFailureKind.motifWithoutLedger /\
            failure.support = entry.support

inductive CannotClaimKind : Type where
  | motifOverlapObjectEquality
  | signatureVectorTheoremEquivalence
  | carryMotifDimension
  | sealMotifCompletionObject
  | completionMotifReal
  | topologyMotifContinuity
  | complexMotifComplexAnalysis
  | bridgeCandidateBridgeCertificate
  | codeExistenceAcceptanceGate

structure CannotClaimEntry where
  kind : CannotClaimKind
  support : EventFlow

def StageCannotClaimAudit
    (P policyFlow : AnalysisProtocolCandidateFlow)
    (required claims : List CannotClaimEntry) : Prop :=
  (exists R : GeneratedAnalysisProtocolRecognizer,
    AnalysisProtocolSubflow R P policyFlow
      AnalysisProtocolRole.cannotClaimPolicy) /\
    forall entry : CannotClaimEntry,
      List.Mem entry required -> List.Mem entry claims

inductive BridgeObligationKind : Type where
  | strongMotifOverlapWithoutBridgeFlow
  | reuseLikeSourceWithoutReuseCert
  | normalAddressWithoutClassifierExactness

structure BridgeObligationCandidate where
  kind : BridgeObligationKind
  source : EventFlow
  target : EventFlow
  support : EventFlow
  evidence : EventFlow
  missingBridge : Not (RecognizedBridgeFlow source target)

def StageBridgeObligationDiscovery
    (P policyFlow S : AnalysisProtocolCandidateFlow)
    (candidates : List BridgeObligationCandidate) : Prop :=
  (exists R : GeneratedAnalysisProtocolRecognizer,
    AnalysisProtocolSubflow R P policyFlow
      AnalysisProtocolRole.bridgeObligationPolicy) /\
    forall candidate : BridgeObligationCandidate,
      List.Mem candidate candidates ->
        EventSubflow candidate.support S /\
          EventSubflow candidate.evidence S /\
          NonemptyEventFlow candidate.support

inductive AnalysisReportKind : Type where
  | motifReport
  | metricReport
  | ledgerAuditReport
  | cannotClaimReport
  | bridgeObligationReport
  | distanceMatrix
  | summaryVisualization

structure AnalysisReportItem where
  kind : AnalysisReportKind
  support : EventFlow

def StageReportGeneration
    (P reportPolicyFlow O : AnalysisProtocolCandidateFlow)
    (items : List AnalysisReportItem) : Prop :=
  (exists R : GeneratedAnalysisProtocolRecognizer,
    AnalysisProtocolSubflow R P reportPolicyFlow
      AnalysisProtocolRole.reportPolicy) /\
    NonemptyEventFlow O /\
    forall item : AnalysisReportItem,
      List.Mem item items -> EventSubflow item.support O

def ReportFlow (O : EventFlow) : Prop :=
  exists P reportPolicyFlow : AnalysisProtocolCandidateFlow,
    exists items : List AnalysisReportItem,
      StageReportGeneration P reportPolicyFlow O items

inductive AnalysisEvidenceKind : Type where
  | proofFlow
  | nameCertFlow
  | derivationCertFlow
  | acceptanceGateFlow

inductive AnalysisOutputDatum : Type where
  | reportFlow (O : EventFlow)
  | evidenceFlow (kind : AnalysisEvidenceKind) (S : EventFlow)

inductive ReportOutputDatum : AnalysisOutputDatum -> Prop where
  | report (O : EventFlow) :
      ReportOutputDatum (AnalysisOutputDatum.reportFlow O)

inductive CertificateEvidenceDatum : AnalysisOutputDatum -> Prop where
  | evidence (kind : AnalysisEvidenceKind) (S : EventFlow) :
      CertificateEvidenceDatum (AnalysisOutputDatum.evidenceFlow kind S)

inductive CertificateObligationKind : Type where
  | nameCert
  | derivationCert
  | acceptanceGate

structure CertificateObligation where
  kind : CertificateObligationKind
  support : EventFlow

def ObligationEvidenceKind :
    CertificateObligationKind -> AnalysisEvidenceKind
  | CertificateObligationKind.nameCert =>
      AnalysisEvidenceKind.nameCertFlow
  | CertificateObligationKind.derivationCert =>
      AnalysisEvidenceKind.derivationCertFlow
  | CertificateObligationKind.acceptanceGate =>
      AnalysisEvidenceKind.acceptanceGateFlow

inductive CertificateObligationDischarge :
    CertificateObligation -> AnalysisOutputDatum -> Prop where
  | evidence (obl : CertificateObligation) :
      CertificateObligationDischarge obl
        (AnalysisOutputDatum.evidenceFlow
          (ObligationEvidenceKind obl.kind) obl.support)

def ContainsMotifReportItem (items : List AnalysisReportItem) : Prop :=
  exists item : AnalysisReportItem,
    List.Mem item items /\ item.kind = AnalysisReportKind.motifReport

def MotifReportOutput (O : EventFlow) : Prop :=
  exists P reportPolicyFlow : AnalysisProtocolCandidateFlow,
    exists items : List AnalysisReportItem,
      StageReportGeneration P reportPolicyFlow O items /\
        ContainsMotifReportItem items

inductive AnalysisFailureKind : Type where
  | illegalChannelStream
  | unrecognizedProtocol
  | uncertifiedRecognizer
  | missingLedger
  | missingCannotClaimEntry
  | undefinedMetric
  | missingClassifierExactness
  | missingBridgeCertificate
  | normalizationWithoutRawLedger
  | sourceChannelConfusion

structure AnalysisFailureItem where
  kind : AnalysisFailureKind
  support : EventFlow

def FailureCompleteReport
    (required recorded : List AnalysisFailureItem) : Prop :=
  forall item : AnalysisFailureItem,
    List.Mem item required -> List.Mem item recorded

structure WellFormedAnalysisRun where
  code : List DisplayAlphabet
  protocol : AnalysisProtocolCandidateFlow
  output : EventFlow
  decoded : EventFlow
  familyFlow : AnalysisProtocolCandidateFlow
  recognizerFamily : List GeneratedRecognizer
  reportPolicyFlow : AnalysisProtocolCandidateFlow
  reportItems : List AnalysisReportItem
  requiredClaims : List CannotClaimEntry
  claims : List CannotClaimEntry
  legalCode : LegalZStream code
  decodedByCode : Decode code = some decoded
  recognizedProtocol : RecognizedAnalysisProtocolFlow protocol
  familyExtracted :
    exists R : GeneratedAnalysisProtocolRecognizer,
      StageRecognizerFamilyExtraction R protocol familyFlow recognizerFamily
  reportGenerated :
    StageReportGeneration protocol reportPolicyFlow output reportItems
  claimsRecorded :
    forall entry : CannotClaimEntry,
      List.Mem entry requiredClaims -> List.Mem entry claims

structure AnalysisOutputDescriptor where
  source : EventFlow
  protocol : AnalysisProtocolCandidateFlow
  recognizerFamily : List GeneratedRecognizer
  stages : List AnalysisStage

def CanonicalAnalysisOutput
    (S : EventFlow) (P : AnalysisProtocolCandidateFlow)
    (Rfam : List GeneratedRecognizer) : AnalysisOutputDescriptor where
  source := S
  protocol := P
  recognizerFamily := Rfam
  stages := AnalysisPipelineStages

def AnalysisDescriptorFromCode
    (c : List DisplayAlphabet) (P : AnalysisProtocolCandidateFlow)
    (Rfam : List GeneratedRecognizer) : Option AnalysisOutputDescriptor :=
  match Decode c with
  | some S => some (CanonicalAnalysisOutput S P Rfam)
  | none => none

inductive FormalAnalysisProtocol :
    AnalysisProtocolCandidateFlow -> Prop where
  | recognized {R : GeneratedAnalysisProtocolRecognizer}
      {P : AnalysisProtocolCandidateFlow} :
      RecognizesAnalysisProtocol R P -> FormalAnalysisProtocol P

theorem unrecognized_protocol_rejected
    {P : AnalysisProtocolCandidateFlow} :
    Not (exists R : GeneratedAnalysisProtocolRecognizer,
      RecognizesAnalysisProtocol R P) ->
      Not (FormalAnalysisProtocol P) := by
  intro hMissing hFormal
  cases hFormal with
  | recognized hRec =>
      exact hMissing ⟨_, hRec⟩

theorem no_external_analysis_config {d : AnalysisConfigDatum} :
    ExternalAnalysisConfig d -> Not (FormalAnalysisConfig d) := by
  intro hExternal hFormal
  cases hExternal <;> cases hFormal

theorem metric_weights_require_protocol_flow
    {P weights : AnalysisProtocolCandidateFlow} :
    Not (MetricWeightsRecordedByProtocol P weights) ->
      Not (FormalWeightedMetric P weights) := by
  intro hMissing hFormal
  cases hFormal with
  | protocol hRecorded =>
      exact hMissing hRecorded

theorem well_formed_analysis_run_source_determined
    (run : WellFormedAnalysisRun) :
    AnalysisDescriptorFromCode run.code run.protocol run.recognizerFamily =
      some
        (CanonicalAnalysisOutput run.decoded run.protocol
          run.recognizerFamily) := by
  rw [AnalysisDescriptorFromCode, run.decodedByCode]

theorem same_decoded_same_protocol_same_output
    {c c' : List DisplayAlphabet} {S P Rfam}
    (hc : Decode c = some S) (hc' : Decode c' = some S) :
    AnalysisDescriptorFromCode c P Rfam =
      AnalysisDescriptorFromCode c' P Rfam := by
  rw [AnalysisDescriptorFromCode, hc, AnalysisDescriptorFromCode, hc']

theorem analysis_roundtrip_invariant
    (S P Rfam) :
    AnalysisDescriptorFromCode (FlowEncoding S) P Rfam =
      some (CanonicalAnalysisOutput S P Rfam) := by
  rw [AnalysisDescriptorFromCode, flow_level_round_trip]

theorem analysis_pipeline_conservativity
    {run : WellFormedAnalysisRun} {w : RawEvent} {m : DisplayAlphabet} :
    List.Mem w run.decoded ->
      List.Mem m w ->
        m = BEDC.FKernel.Mark.BMark.b0 \/
          m = BEDC.FKernel.Mark.BMark.b1 := by
  intro _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

theorem non_failure_complete_inadmissible
    {required recorded : List AnalysisFailureItem}
    {item : AnalysisFailureItem} :
    List.Mem item required ->
      Not (List.Mem item recorded) ->
        Not (FailureCompleteReport required recorded) := by
  intro hRequired hOmitted hComplete
  exact hOmitted (hComplete item hRequired)

theorem bridge_obligation_not_bridge
    (candidate : BridgeObligationCandidate) :
    Not (RecognizedBridgeFlow candidate.source candidate.target) :=
  candidate.missingBridge

theorem bridge_discovery_noncommittal
    {P policyFlow S : AnalysisProtocolCandidateFlow}
    {candidates : List BridgeObligationCandidate}
    {candidate : BridgeObligationCandidate} :
    StageBridgeObligationDiscovery P policyFlow S candidates ->
      List.Mem candidate candidates ->
        Not (RecognizedBridgeFlow candidate.source candidate.target) := by
  intro _ _
  exact candidate.missingBridge

theorem reports_not_evidence {d : AnalysisOutputDatum} :
    ReportOutputDatum d -> Not (CertificateEvidenceDatum d) := by
  intro hReport hEvidence
  cases hReport
  cases hEvidence

theorem report_cannot_discharge_certificate_obligation
    {obl : CertificateObligation} {O : EventFlow} :
    Not
      (CertificateObligationDischarge obl
        (AnalysisOutputDatum.reportFlow O)) := by
  intro h
  cases h

theorem motif_report_cannot_license_mature_object
    {O : EventFlow} :
    MotifReportOutput O ->
      Not
        (CertificateObligationDischarge
          { kind := CertificateObligationKind.acceptanceGate,
            support := O }
          (AnalysisOutputDatum.reportFlow O)) := by
  intro _ h
  cases h

end BEDC.GroundCompiler.AnalysisPipeline
