import BEDC.GroundCompiler.MetricsFlow

namespace BEDC.GroundCompiler.MetricsFlow

open BEDC.GroundCompiler.EventFlow

structure P4AuditChecklist
    (metricSpecFlow : MetricSpecificationFlow) (metricSpec : MetricSpec)
    (sourceFlow protocolFlow : EventFlow) (report : MetricReport) where
  soundMetricReport : MetricReportSoundness report
  recognizedMetricProtocol : MetricProtocolFlow protocolFlow
  metricsAdmissible :
    AdmissibleMetric metricSpecFlow metricSpec sourceFlow protocolFlow
  candidateRecognizedSeparated :
    exists candidates recognized : List MotifOccurrence,
      exists role : EventFlow,
        Not (CandidateMotifCount candidates role =
          RecognizedMotifCount recognized role)
  missingRecognizerExplicit :
    forall role : EventFlow,
      RecognizedMotifCountStatus none role =
        MotifCountStatus.recognizerMissing
  cannotClaimsIncluded : CannotClaimGuardedReport report
  externalMetricInputsRejected :
    forall d : MetricDataKind, MetricExternalInput d -> Not (MetricAllowedData d)

structure P4Adequate
    (metricSpecFlow : MetricSpecificationFlow) (metricSpec : MetricSpec)
    (sourceFlow protocolFlow : EventFlow) (report : MetricReport) where
  audit :
    P4AuditChecklist metricSpecFlow metricSpec sourceFlow protocolFlow report
  sourceFlowsAreFormal :
    forall S : EventFlow,
      List.Mem S report.sourceFlows ->
        FormalCompilerInput (CompilerDatum.eventFlow S)
  undefinedMetricsRecorded :
    forall item : UndefinedMetricItem,
      List.Mem item report.undefinedItems ->
        ReportHasUndefinedMetricItem report item
  protocolRecognized : MetricProtocolFlow protocolFlow
  metricsAdmissible :
    AdmissibleMetric metricSpecFlow metricSpec sourceFlow protocolFlow
  cannotClaimsGuarded : CannotClaimGuardedReport report

theorem p4_adequacy
    {metricSpecFlow : MetricSpecificationFlow} {metricSpec : MetricSpec}
    {sourceFlow protocolFlow : EventFlow} {report : MetricReport} :
    P4AuditChecklist metricSpecFlow metricSpec sourceFlow protocolFlow report ->
      P4Adequate metricSpecFlow metricSpec sourceFlow protocolFlow report := by
  intro hAudit
  exact
    { audit := hAudit,
      sourceFlowsAreFormal := hAudit.soundMetricReport.sourceFlowsAreFormal,
      undefinedMetricsRecorded :=
        hAudit.soundMetricReport.undefinedMetricsRecorded,
      protocolRecognized := hAudit.recognizedMetricProtocol,
      metricsAdmissible := hAudit.metricsAdmissible,
      cannotClaimsGuarded := hAudit.cannotClaimsIncluded }

theorem p4_adequacy_not_higher :
    exists metricSpecFlow : MetricSpecificationFlow,
      exists metricSpec : MetricSpec,
        exists sourceFlow protocolFlow : EventFlow,
          exists report : MetricReport,
            P4Adequate metricSpecFlow metricSpec sourceFlow protocolFlow report /\
              Not (AcceptedObjectFlow sourceFlow) := by
  let report : MetricReport :=
    { protocol :=
        { protocolFlow := [],
          weights :=
            { motifWeight := 0,
              normalAddressWeight := 0,
              prefixWeight := 0,
              ledgerWeight := 0,
              reuseWeight := 0 } },
      recognizers := [],
      sourceFlows := [[]],
      signatures := [],
      undefinedItems := [],
      cannotClaims := [] }
  let metricSpec : MetricSpec := { sources := [] }
  have hSpecRecognized : RecognizedMetricSpec [] :=
    ⟨[], FormalCompilerInput.recognizedFlow [] []⟩
  have hProtocolRecognized : MetricProtocolFlow [] :=
    ⟨[], FormalCompilerInput.recognizedFlow [] []⟩
  have hMetricAdmissible : AdmissibleMetric [] metricSpec [] [] :=
    And.intro (FormalCompilerInput.eventFlow [])
      (And.intro hSpecRecognized
        (And.intro hProtocolRecognized
          (fun d hMem => by cases hMem)))
  have hSourceFlowsFormal :
      forall S : EventFlow,
        List.Mem S report.sourceFlows ->
          FormalCompilerInput (CompilerDatum.eventFlow S) := by
    intro S hMem
    cases hMem with
    | head =>
        exact FormalCompilerInput.eventFlow []
    | tail _ hTail =>
        cases hTail
  have hUndefinedRecorded :
      forall item : UndefinedMetricItem,
        List.Mem item report.undefinedItems ->
          ReportHasUndefinedMetricItem report item := by
    intro item hMem
    cases hMem
  have hCannotClaimsGuarded : CannotClaimGuardedReport report := by
    intro hNontrivial
    cases hNontrivial with
    | intro sig hSig =>
        cases hSig.left
  have hSound : MetricReportSoundness report :=
    { sourceFlowsAreFormal := hSourceFlowsFormal,
      undefinedMetricsRecorded := hUndefinedRecorded,
      cannotClaimsGuarded := hCannotClaimsGuarded }
  have hAudit : P4AuditChecklist [] metricSpec [] [] report :=
    { soundMetricReport := hSound,
      recognizedMetricProtocol := hProtocolRecognized,
      metricsAdmissible := hMetricAdmissible,
      candidateRecognizedSeparated := candidate_count_weaker,
      missingRecognizerExplicit := fun _ => rfl,
      cannotClaimsIncluded := hSound.cannotClaimsGuarded,
      externalMetricInputsRejected :=
        fun _ hExternal => external_metric_input_not_allowed hExternal }
  exact
    ⟨[], metricSpec, [], [], report,
      And.intro (p4_adequacy hAudit) empty_not_accepted_object_flow⟩

end BEDC.GroundCompiler.MetricsFlow
