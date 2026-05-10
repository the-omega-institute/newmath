import BEDC.GroundCompiler.MetricsFlow

namespace BEDC.GroundCompiler.MetricsFlow

open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

def P4ReportGenerator : Type :=
  EventFlow -> EventFlow -> MetricReport

structure P4Pipeline (generator : P4ReportGenerator)
    (channelCode : List DisplayAlphabet) (protocolFlow : EventFlow) where
  sourceFlow : EventFlow
  sourceDecoded : Decode channelCode = some sourceFlow
  protocolRecognized : MetricProtocolFlow protocolFlow

def P4PipelineOutput {generator : P4ReportGenerator}
    {channelCode : List DisplayAlphabet} {protocolFlow : EventFlow}
    (run : P4Pipeline generator channelCode protocolFlow) : MetricReport :=
  generator run.sourceFlow protocolFlow

theorem p4_source_determined_relative_to_protocol
    {generator : P4ReportGenerator} {channelCode : List DisplayAlphabet}
    {protocolFlow sourceLeft sourceRight : EventFlow} :
    Decode channelCode = some sourceLeft ->
      Decode channelCode = some sourceRight ->
        sourceLeft = sourceRight /\
          generator sourceLeft protocolFlow = generator sourceRight protocolFlow := by
  intro hLeft hRight
  have hSourceOpt : some sourceLeft = some sourceRight :=
    Eq.trans (Eq.symm hLeft) hRight
  have hSource : sourceLeft = sourceRight := by
    cases hSourceOpt
    rfl
  constructor
  · exact hSource
  · cases hSource
    rfl

def ZeroTheoryDistanceWeights : TheoryDistanceWeights where
  motifWeight := 0
  normalAddressWeight := 0
  prefixWeight := 0
  ledgerWeight := 0
  reuseWeight := 0

def MinimalAnalysisProtocol (protocolFlow : EventFlow) : AnalysisProtocolFlow where
  protocolFlow := protocolFlow
  weights := ZeroTheoryDistanceWeights

def MinimalP4Report (sourceFlow protocolFlow : EventFlow) : MetricReport where
  protocol := MinimalAnalysisProtocol protocolFlow
  recognizers := []
  sourceFlows := [sourceFlow]
  signatures := [EmptyAnalysisSignature sourceFlow]
  undefinedItems := []
  cannotClaims := []

theorem different_protocols_may_yield_different_reports :
    exists S P Q : EventFlow,
      Not (P = Q) /\
        Not ((MinimalP4Report S P).protocol.protocolFlow =
          (MinimalP4Report S Q).protocol.protocolFlow) := by
  refine ⟨[], [], [[]], ?_, ?_⟩
  · intro h
    cases h
  · intro h
    change [] = [[]] at h
    cases h

end BEDC.GroundCompiler.MetricsFlow
