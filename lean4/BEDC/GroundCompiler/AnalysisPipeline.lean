import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.AnalysisPipeline

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

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

end BEDC.GroundCompiler.AnalysisPipeline
