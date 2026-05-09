import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.MetricsFlow

open BEDC.GroundCompiler.ChannelEncoding
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

structure ClassifierCompressionData where
  rawSupportFlows : List EventFlow
  classifierClasses : List EventFlow
  classifierRecognition : MetricAllowedData MetricDataKind.recognizedClassifier
  ledgerRecognition : MetricAllowedData MetricDataKind.recognizedLedger
  exactnessRecognition : EventFlow
  classCountPositive : 0 < classifierClasses.length

def CompressionRatio (q : ClassifierCompressionData) : Nat × Nat :=
  (q.rawSupportFlows.length, q.classifierClasses.length)

structure ReuseChain where
  links : List EventFlow
  recognizer : GeneratedRecognizer
  allLinksRecognized :
    forall M : EventFlow,
      List.Mem M links ->
        FormalCompilerInput (CompilerDatum.recognizedFlow recognizer M)

def ReuseDepth (chains : List ReuseChain) : Nat :=
  (chains.map (fun chain => chain.links.length)).foldr Nat.max 0

structure BridgeChain where
  sourceFlow : EventFlow
  targetFlow : EventFlow
  steps : List EventFlow
  recognizer : GeneratedRecognizer
  sourceRecognized :
    FormalCompilerInput (CompilerDatum.recognizedFlow recognizer sourceFlow)
  targetRecognized :
    FormalCompilerInput (CompilerDatum.recognizedFlow recognizer targetFlow)
  allStepsRecognized :
    forall step : EventFlow,
      List.Mem step steps ->
        FormalCompilerInput (CompilerDatum.recognizedFlow recognizer step)

def BridgeDepth (chains : List BridgeChain) : Nat :=
  (chains.map (fun chain => chain.steps.length)).foldr Nat.max 0

structure NormalAddressRecord where
  sourceFlow : EventFlow
  normalFlow : EventFlow
  ledgerFlow : EventFlow
  deriving DecidableEq

def NormalAddressMap
    (Rfam : MetricRecognizerFamily) (S : EventFlow)
    (records : List NormalAddressRecord) : Prop :=
  forall rec : NormalAddressRecord,
    List.Mem rec records ->
      EventSubflow S rec.sourceFlow /\
        EventSubflow S rec.normalFlow /\
        EventSubflow S rec.ledgerFlow /\
        exists R : GeneratedRecognizer,
          List.Mem R Rfam /\
            FormalCompilerInput
              (CompilerDatum.recognizedFlow R rec.sourceFlow) /\
            FormalCompilerInput
              (CompilerDatum.recognizedFlow R rec.normalFlow) /\
            FormalCompilerInput
              (CompilerDatum.recognizedFlow R rec.ledgerFlow)

def ListContains {α : Type} [DecidableEq α] (x : α) : List α -> Bool
  | [] => false
  | y :: ys => if x = y then true else ListContains x ys

def ListIntersectionCount {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  (xs.filter (fun x => ListContains x ys)).length

def ListUnionCount {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  xs.length + (ys.filter (fun y => not (ListContains y xs))).length

def JaccardDistanceRatio {α : Type} [DecidableEq α] (xs ys : List α) :
    Nat × Nat :=
  let unionCount := ListUnionCount xs ys
  (unionCount - ListIntersectionCount xs ys, unionCount)

def NormalAddressDistance
    (left right : List NormalAddressRecord) : Nat × Nat :=
  JaccardDistanceRatio left right

def MotifJaccardDistance
    (left right : List MotifOccurrence) : Nat × Nat :=
  JaccardDistanceRatio left right

structure FlowSignatureVector where
  sealDepth : Nat
  carryIndex : Nat
  ledgerDepth : Nat
  compressionNumerator : Nat
  compressionDenominator : Nat
  reuseDepth : Nat
  bridgeDepth : Nat

def FlowSignature
    (profile : List MotifOccurrence) (sealRole carryRole : EventFlow)
    (ledgerDepths : List Nat) (compression : Nat × Nat)
    (reuseChains : List ReuseChain) (bridgeChains : List BridgeChain) :
    FlowSignatureVector where
  sealDepth := SealDepth profile sealRole
  carryIndex := CarryIndex profile carryRole
  ledgerDepth := LedgerDepth ledgerDepths
  compressionNumerator := compression.fst
  compressionDenominator := compression.snd
  reuseDepth := ReuseDepth reuseChains
  bridgeDepth := BridgeDepth bridgeChains

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

theorem channel_substring_metrics_inadmissible :
    Not (MetricAdmissible
      { sources := [MetricDataKind.channelSubstring] }) := by
  intro hAdmissible
  exact
    external_metric_input_not_allowed
      MetricExternalInput.channelSubstring
      (hAdmissible MetricDataKind.channelSubstring (List.Mem.head []))

theorem metrics_channel_roundtrip_invariant
    {α : Type} (M : EventFlow -> α) (S : EventFlow) :
    Option.map M (Decode (FlowEncoding S)) = some (M S) := by
  rw [flow_level_round_trip]
  rfl

end BEDC.GroundCompiler.MetricsFlow
