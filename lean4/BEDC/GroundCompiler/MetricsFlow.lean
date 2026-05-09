import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.MetricsFlow

open BEDC.GroundCompiler.EventFlow

deriving instance DecidableEq for DisplayAlphabet
deriving instance DecidableEq for RawEvent
deriving instance DecidableEq for EventFlow
deriving instance DecidableEq for GeneratedRecognizer

inductive MetricCandidate : Type where
  | scalar (value : Nat)
  | sequence (values : List Nat)
  | finiteSet (values : List Nat)
  | summary (values : List Nat)

def GeneratedMetricRecognizer : Type :=
  EventFlow

def MetricSpecificationFlow : Type :=
  EventFlow

def RecognizesMetric
    (R : GeneratedMetricRecognizer) (m : MetricSpecificationFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R m)

def MetricProtocolFlow (Pmet : EventFlow) : Prop :=
  exists R : GeneratedMetricRecognizer, RecognizesMetric R Pmet

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

def RawPrefixProfile (S P : EventFlow) : Prop :=
  exists rest : EventFlow, S = List.append P rest

def RawPrefixOverlapLength : EventFlow -> EventFlow -> Nat
  | [], _ => 0
  | _, [] => 0
  | w :: S, v :: T =>
      if w = v then Nat.succ (RawPrefixOverlapLength S T) else 0

def RecognizedPrefixProfile
    (Rfam : MetricRecognizerFamily) (S P role ledger : EventFlow) : Prop :=
  RawPrefixProfile S P /\
    exists R : GeneratedRecognizer,
      List.Mem R Rfam /\
        FormalCompilerInput (CompilerDatum.recognizedFlow R P) /\
        FormalCompilerInput (CompilerDatum.recognizedFlow R role) /\
        FormalCompilerInput (CompilerDatum.recognizedFlow R ledger)

def RecognizedPrefixOverlap
    (Rfam : MetricRecognizerFamily) (S T P role ledger : EventFlow) : Prop :=
  RecognizedPrefixProfile Rfam S P role ledger /\
    RecognizedPrefixProfile Rfam T P role ledger

structure MotifOccurrence where
  role : EventFlow
  support : EventFlow
  ledger : EventFlow
  recognizer : GeneratedRecognizer
  deriving DecidableEq

def EventSubflow (S M : EventFlow) : Prop :=
  exists pre post : EventFlow, S = List.append pre (List.append M post)

def MotifOccurrenceRecognized
    (Rfam : MetricRecognizerFamily) (S : EventFlow) (occ : MotifOccurrence) :
    Prop :=
  EventSubflow S occ.support /\
    List.Mem occ.recognizer Rfam /\
    FormalCompilerInput (CompilerDatum.recognizedFlow occ.recognizer occ.support) /\
    FormalCompilerInput (CompilerDatum.recognizedFlow occ.recognizer occ.role) /\
    FormalCompilerInput (CompilerDatum.recognizedFlow occ.recognizer occ.ledger)

def MotifProfile
    (Rfam : MetricRecognizerFamily) (S : EventFlow)
    (profile : List MotifOccurrence) : Prop :=
  forall occ : MotifOccurrence,
    List.Mem occ profile -> MotifOccurrenceRecognized Rfam S occ

def MotifMultiplicity (profile : List MotifOccurrence) (role : EventFlow) : Nat :=
  (profile.filter (fun occ => decide (occ.role = role))).length

def SealDepth (profile : List MotifOccurrence) (sealRole : EventFlow) : Nat :=
  MotifMultiplicity profile sealRole

def CarryIndex (profile : List MotifOccurrence) (carryRole : EventFlow) : Nat :=
  MotifMultiplicity profile carryRole

def LedgerDepth (ledgerDepths : List Nat) : Nat :=
  ledgerDepths.foldr Nat.max 0

theorem external_metric_input_not_allowed {d : MetricDataKind} :
    MetricExternalInput d -> Not (MetricAllowedData d) := by
  intro hExternal hAllowed
  cases hExternal <;> cases hAllowed

theorem raw_prefix_weaker :
    (forall {Rfam : MetricRecognizerFamily} {S T P role ledger : EventFlow},
      RecognizedPrefixOverlap Rfam S T P role ledger ->
        RawPrefixProfile S P /\ RawPrefixProfile T P) /\
      exists S T P : EventFlow,
        RawPrefixProfile S P /\
          RawPrefixProfile T P /\
          Not (exists role ledger : EventFlow,
            RecognizedPrefixOverlap [] S T P role ledger) := by
  constructor
  · intro Rfam S T P role ledger hOverlap
    exact ⟨hOverlap.left.left, hOverlap.right.left⟩
  · refine ⟨[], [], [], ?_, ?_, ?_⟩
    · exact ⟨[], rfl⟩
    · exact ⟨[], rfl⟩
    · intro hRecognized
      cases hRecognized with
      | intro role hRole =>
          cases hRole with
          | intro ledger hOverlap =>
              cases hOverlap.left.right with
              | intro R hR =>
                  cases hR.left

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
