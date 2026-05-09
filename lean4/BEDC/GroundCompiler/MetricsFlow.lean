import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.MetricsFlow

open BEDC.GroundCompiler.EventFlow

def MetricRecognizerFamily : Type :=
  List GeneratedRecognizer

inductive MetricDataKind : Type where
  | decodedSourceFlow
  | recognizedMotif
  | recognizedLedger
  | recognizedClassifier
  | recognizedReuse
  | recognizedNormalAddress
  | failureFlow
  | cannotClaimFlow
  | channelSubstring
  | externalObjectName
  | yamlField
  | hostAST
  | theoremLabel
  | chapterTitle
  | externalSemanticCategory
  | unrecordedClassifierJudgment

structure MetricSpec where
  sources : List MetricDataKind

inductive MetricAllowedData : MetricDataKind -> Prop where
  | decodedSourceFlow :
      MetricAllowedData MetricDataKind.decodedSourceFlow
  | recognizedMotif :
      MetricAllowedData MetricDataKind.recognizedMotif
  | recognizedLedger :
      MetricAllowedData MetricDataKind.recognizedLedger
  | recognizedClassifier :
      MetricAllowedData MetricDataKind.recognizedClassifier
  | recognizedReuse :
      MetricAllowedData MetricDataKind.recognizedReuse
  | recognizedNormalAddress :
      MetricAllowedData MetricDataKind.recognizedNormalAddress
  | failureFlow :
      MetricAllowedData MetricDataKind.failureFlow
  | cannotClaimFlow :
      MetricAllowedData MetricDataKind.cannotClaimFlow

inductive MetricExternalInput : MetricDataKind -> Prop where
  | channelSubstring :
      MetricExternalInput MetricDataKind.channelSubstring
  | externalObjectName :
      MetricExternalInput MetricDataKind.externalObjectName
  | yamlField :
      MetricExternalInput MetricDataKind.yamlField
  | hostAST :
      MetricExternalInput MetricDataKind.hostAST
  | theoremLabel :
      MetricExternalInput MetricDataKind.theoremLabel
  | chapterTitle :
      MetricExternalInput MetricDataKind.chapterTitle
  | externalSemanticCategory :
      MetricExternalInput MetricDataKind.externalSemanticCategory
  | unrecordedClassifierJudgment :
      MetricExternalInput MetricDataKind.unrecordedClassifierJudgment

def MetricAdmissible (M : MetricSpec) : Prop :=
  forall d : MetricDataKind, List.Mem d M.sources -> MetricAllowedData d

theorem external_metric_input_not_allowed {d : MetricDataKind} :
    MetricExternalInput d -> Not (MetricAllowedData d) := by
  intro hExternal hAllowed
  cases hExternal <;> cases hAllowed

theorem no_external_metric_input {M : MetricSpec} :
    MetricAdmissible M ->
      forall d : MetricDataKind,
        List.Mem d M.sources -> Not (MetricExternalInput d) := by
  intro hAdmissible d hd hExternal
  exact external_metric_input_not_allowed hExternal (hAdmissible d hd)

theorem external_object_name_metric_inadmissible :
    Not (MetricAdmissible
      { sources := [MetricDataKind.externalObjectName] }) := by
  intro hAdmissible
  exact
    external_metric_input_not_allowed
      MetricExternalInput.externalObjectName
      (hAdmissible MetricDataKind.externalObjectName (List.Mem.head []))

end BEDC.GroundCompiler.MetricsFlow
