import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.ProgrammaticRealization

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

inductive ChannelDFAState : Type where
  | boundary
  | body
  | sawOne
  | dead

def ChannelDFAStep : ChannelDFAState -> DisplayAlphabet -> ChannelDFAState
  | ChannelDFAState.boundary, BMark.b0 => ChannelDFAState.body
  | ChannelDFAState.boundary, BMark.b1 => ChannelDFAState.sawOne
  | ChannelDFAState.body, BMark.b0 => ChannelDFAState.body
  | ChannelDFAState.body, BMark.b1 => ChannelDFAState.sawOne
  | ChannelDFAState.sawOne, BMark.b0 => ChannelDFAState.body
  | ChannelDFAState.sawOne, BMark.b1 => ChannelDFAState.boundary
  | ChannelDFAState.dead, _ => ChannelDFAState.dead

def ChannelDFARun : ChannelDFAState -> List DisplayAlphabet -> ChannelDFAState
  | q, [] => q
  | q, m :: rest => ChannelDFARun (ChannelDFAStep q m) rest

def ChannelDFAAccept (c : List DisplayAlphabet) : Prop :=
  ChannelDFARun ChannelDFAState.boundary c = ChannelDFAState.boundary

structure ExecutableChannelCore where
  encodeMark : DisplayAlphabet -> List DisplayAlphabet
  encodeEvent : RawEvent -> List DisplayAlphabet
  encodeFlow : EventFlow -> List DisplayAlphabet
  decode : List DisplayAlphabet -> Option EventFlow
  markZero : encodeMark BMark.b0 = [BMark.b0]
  markOne : encodeMark BMark.b1 = [BMark.b1, BMark.b0]
  event_eq : forall w : RawEvent, encodeEvent w = EventEncoding w
  flow_eq : forall S : EventFlow, encodeFlow S = FlowEncoding S
  decode_eq : forall c : List DisplayAlphabet, decode c = Decode c

def referenceExecutableChannelCore : ExecutableChannelCore where
  encodeMark
    | BMark.b0 => [BMark.b0]
    | BMark.b1 => [BMark.b1, BMark.b0]
  encodeEvent := EventEncoding
  encodeFlow := FlowEncoding
  decode := Decode
  markZero := rfl
  markOne := rfl
  event_eq := by
    intro _
    rfl
  flow_eq := by
    intro _
    rfl
  decode_eq := by
    intro _
    rfl

theorem channel_dfa_run_append
    (q : ChannelDFAState) (xs ys : List DisplayAlphabet) :
    ChannelDFARun q (xs ++ ys) = ChannelDFARun (ChannelDFARun q xs) ys := by
  induction xs generalizing q with
  | nil =>
      rfl
  | cons m rest ih =>
      change
        ChannelDFARun (ChannelDFAStep q m) (rest ++ ys) =
          ChannelDFARun (ChannelDFARun (ChannelDFAStep q m) rest) ys
      exact ih (ChannelDFAStep q m)

theorem event_encoding_dfa_accepts_from_boundary_and_body
    (w : RawEvent) :
    ChannelDFARun ChannelDFAState.boundary (EventEncoding w) =
      ChannelDFAState.boundary /\
    ChannelDFARun ChannelDFAState.body (EventEncoding w) =
      ChannelDFAState.boundary := by
  induction w with
  | nil =>
      constructor
      · rfl
      · rfl
  | cons m rest ih =>
      cases m with
      | b0 =>
          constructor
          · change
              ChannelDFARun ChannelDFAState.body (EventEncoding rest) =
                ChannelDFAState.boundary
            exact ih.right
          · change
              ChannelDFARun ChannelDFAState.body (EventEncoding rest) =
                ChannelDFAState.boundary
            exact ih.right
      | b1 =>
          constructor
          · change
              ChannelDFARun ChannelDFAState.body (EventEncoding rest) =
                ChannelDFAState.boundary
            exact ih.right
          · change
              ChannelDFARun ChannelDFAState.body (EventEncoding rest) =
                ChannelDFAState.boundary
            exact ih.right

theorem flow_encoding_dfa_accepts (S : EventFlow) :
    ChannelDFAAccept (FlowEncoding S) := by
  induction S with
  | nil =>
      rfl
  | cons w rest ih =>
      change
        ChannelDFARun ChannelDFAState.boundary
          (EventEncoding w ++ FlowEncoding rest) = ChannelDFAState.boundary
      rw [channel_dfa_run_append]
      rw [(event_encoding_dfa_accepts_from_boundary_and_body w).left]
      exact ih

theorem base_language_stream_regular {c : List DisplayAlphabet} :
    LegalZStream c -> ChannelDFAAccept c := by
  intro hLegal
  cases hLegal with
  | intro S hS =>
      rw [hS]
      exact flow_encoding_dfa_accepts S

structure ExecutableP0Realization where
  core : ExecutableChannelCore
  legal : List DisplayAlphabet -> Prop
  legal_eq : forall c : List DisplayAlphabet, legal c <-> LegalZStream c
  roundTrip : forall S : EventFlow, core.decode (core.encodeFlow S) = some S

def referenceExecutableP0Realization : ExecutableP0Realization where
  core := referenceExecutableChannelCore
  legal := LegalZStream
  legal_eq := by
    intro c
    constructor
    · intro h
      exact h
    · intro h
      exact h
  roundTrip := by
    intro S
    exact flow_level_round_trip S

def AdjacentPairReport : EventFlow -> List (RawEvent × RawEvent)
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      (first, second) :: AdjacentPairReport (second :: rest)

structure ExecutableReportLayer where
  sourceReport : EventFlow -> EventFlow
  adjacentPairReport : EventFlow -> List (RawEvent × RawEvent)
  motifCandidateReport : EventFlow -> List EventFlow
  metricReport : EventFlow -> List Nat

def referenceExecutableReportLayer : ExecutableReportLayer where
  sourceReport := fun S => S
  adjacentPairReport := AdjacentPairReport
  motifCandidateReport := fun S => List.map (fun w => [w]) S
  metricReport := fun S => [S.length]

inductive ReportClassification : Type where
  | candidateShape (S : EventFlow)
  | recognizedStructure (R : GeneratedRecognizer) (S : EventFlow)

def EvidenceBackedReport (j : ReportClassification) : Prop :=
  exists R : GeneratedRecognizer, exists S : EventFlow,
    j = ReportClassification.recognizedStructure R S /\
      FormalCompilerInput (CompilerDatum.recognizedFlow R S)

theorem programs_do_not_upgrade_candidates (S : EventFlow) :
    Not (EvidenceBackedReport (ReportClassification.candidateShape S)) := by
  intro h
  cases h with
  | intro R hR =>
      cases hR with
      | intro T hT =>
          cases hT.left

theorem p1_p4_executable :
    exists L : ExecutableReportLayer,
      L.sourceReport [] = [] /\
        L.adjacentPairReport [[BMark.b0], [BMark.b1], [BMark.b0]] =
          [([BMark.b0], [BMark.b1]), ([BMark.b1], [BMark.b0])] /\
        L.motifCandidateReport [[BMark.b0], [BMark.b1]] =
          [[[BMark.b0]], [[BMark.b1]]] /\
        L.metricReport [[BMark.b0], [BMark.b1]] = [2] := by
  refine ⟨referenceExecutableReportLayer, ?_⟩
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

structure RecognizerVMInput where
  ambient : EventFlow
  recognizer : GeneratedRecognizer
  support : Option EventFlow

inductive RecognizerVMOutputDatum : Type where
  | recognitionJudgment (R : GeneratedRecognizer) (S : EventFlow)
  | ledgerRecord (S : EventFlow)
  | missingFieldRecord (S : EventFlow)
  | failureRecord (S : EventFlow)
  | cannotClaimAnnotation (S : EventFlow)

structure RecognizerVirtualMachine where
  run : RecognizerVMInput -> List RecognizerVMOutputDatum

def referenceRecognizerVirtualMachine : RecognizerVirtualMachine where
  run := fun input =>
    [RecognizerVMOutputDatum.recognitionJudgment input.recognizer input.ambient]

inductive RecognizerProgramArtifact : Type where
  | hostInterpreter (M : RecognizerVirtualMachine)
  | eventFlowRecognizer (R : GeneratedRecognizer) (S : EventFlow)
  | recognizerCertificate (C : EventFlow)
  | recognizerLedger (L : EventFlow)
  | recognizerFailureBehavior (F : EventFlow)

inductive FormalRecognizerEvidence : RecognizerProgramArtifact -> Prop where
  | eventFlowRecognizer
      (R : GeneratedRecognizer) (S : EventFlow) :
      FormalCompilerInput (CompilerDatum.recognizedFlow R S) ->
        FormalRecognizerEvidence
          (RecognizerProgramArtifact.eventFlowRecognizer R S)
  | recognizerCertificate (C : EventFlow) :
      FormalCompilerInput (CompilerDatum.eventFlow C) ->
        FormalRecognizerEvidence
          (RecognizerProgramArtifact.recognizerCertificate C)
  | recognizerLedger (L : EventFlow) :
      FormalCompilerInput (CompilerDatum.eventFlow L) ->
        FormalRecognizerEvidence
          (RecognizerProgramArtifact.recognizerLedger L)
  | recognizerFailureBehavior (F : EventFlow) :
      FormalCompilerInput (CompilerDatum.eventFlow F) ->
        FormalRecognizerEvidence
          (RecognizerProgramArtifact.recognizerFailureBehavior F)

def RecognizerVMDiscipline (_M : RecognizerVirtualMachine) : Prop :=
  (forall d : CompilerDatum,
    StructuralHiddenInput d -> Not (FormalCompilerInput d)) /\
    (forall S : EventFlow,
      Not (EvidenceBackedReport (ReportClassification.candidateShape S)))

def RecognizerVMRealizesP5P8Interface
    (M : RecognizerVirtualMachine) : Prop :=
  RecognizerVMDiscipline M /\
    Not (FormalCompilerInput CompilerDatum.hostPkg) /\
    Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
    Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
    Not (FormalCompilerInput CompilerDatum.hostChapterPkg) /\
    Not (FormalCompilerInput CompilerDatum.hostManifest)

theorem vm_not_evidence (M : RecognizerVirtualMachine) :
    Not
      (FormalRecognizerEvidence
        (RecognizerProgramArtifact.hostInterpreter M)) := by
  intro h
  cases h

theorem vm_realizes_p5_p8 :
    RecognizerVMRealizesP5P8Interface referenceRecognizerVirtualMachine := by
  constructor
  · constructor
    · intro _ hHidden
      exact structural_hidden_not_formal hHidden
    · intro S
      exact programs_do_not_upgrade_candidates S
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
    · constructor
      · exact structural_hidden_not_formal StructuralHiddenInput.hostNameCert
      · constructor
        · exact structural_hidden_not_formal
            StructuralHiddenInput.hostTheoremIdentifier
        · constructor
          · exact structural_hidden_not_formal StructuralHiddenInput.hostChapterPkg
          · exact structural_hidden_not_formal StructuralHiddenInput.hostManifest

structure CertificateCheckerLayer where
  checksNameCert : EventFlow -> Prop
  checksDerivCert : EventFlow -> Prop
  checksAcceptGate : EventFlow -> Prop
  checksTheoremProof : EventFlow -> Prop
  checksChapterManuscript : EventFlow -> Prop
  checksCompilerGlobal : EventFlow -> Prop

inductive CheckerLayerArtifact : Type where
  | hostChecker (L : CertificateCheckerLayer)
  | certificateFlow (C : EventFlow)
  | proofFlow (P : EventFlow)
  | acceptedObjectFlow (S : EventFlow)
  | theoremFlow (T : EventFlow)

inductive FormalCheckerEvidence : CheckerLayerArtifact -> Prop where
  | certificateFlow (C : EventFlow) :
      FormalCompilerInput (CompilerDatum.eventFlow C) ->
        FormalCheckerEvidence (CheckerLayerArtifact.certificateFlow C)
  | proofFlow (P : EventFlow) :
      FormalCompilerInput (CompilerDatum.eventFlow P) ->
        FormalCheckerEvidence (CheckerLayerArtifact.proofFlow P)
  | acceptedObjectFlow (S : EventFlow) :
      AcceptedObjectFlow S ->
        FormalCheckerEvidence (CheckerLayerArtifact.acceptedObjectFlow S)
  | theoremFlow (T : EventFlow) :
      RecognizedTheoremFlow T ->
        FormalCheckerEvidence (CheckerLayerArtifact.theoremFlow T)

theorem checker_program_not_certificate_evidence
    (L : CertificateCheckerLayer) :
    Not (FormalCheckerEvidence (CheckerLayerArtifact.hostChecker L)) := by
  intro h
  cases h

inductive ProgramAcceptedEmission : EventFlow -> Prop where
  | objectCode {S : EventFlow} :
      AcceptedObjectFlow S -> ProgramAcceptedEmission S
  | theoremCode {T : EventFlow} :
      RecognizedTheoremFlow T -> ProgramAcceptedEmission T

theorem acceptance_certificate_mediated {S : EventFlow} :
    ProgramAcceptedEmission S ->
      AcceptedObjectFlow S \/ RecognizedTheoremFlow S := by
  intro h
  cases h with
  | objectCode hObj =>
      exact Or.inl hObj
  | theoremCode hThm =>
      exact Or.inr hThm

structure ProgrammaticSelfHostingRoute where
  hostReferenceRuntime : EventFlow
  channelAndRecognizerRules : EventFlow
  recognizerVMFlow : EventFlow
  compilerRecognitionFlow : EventFlow
  compilerCertificateFlow : EventFlow
  selfCompilationFlow : EventFlow
  behaviorEquivalenceFlow : EventFlow
  bootstrapObligationFlow : EventFlow

inductive SelfHostingClaimArtifact : Type where
  | hostExecution (runtime compilerDescription : EventFlow)
  | certifiedRoute (route : ProgrammaticSelfHostingRoute)

inductive CompleteSelfHostingEvidence : SelfHostingClaimArtifact -> Prop where
  | certifiedRoute (route : ProgrammaticSelfHostingRoute) :
      FormalCompilerInput (CompilerDatum.eventFlow route.compilerRecognitionFlow) ->
        FormalCompilerInput (CompilerDatum.eventFlow route.compilerCertificateFlow) ->
          FormalCompilerInput (CompilerDatum.eventFlow route.selfCompilationFlow) ->
            FormalCompilerInput
              (CompilerDatum.eventFlow route.behaviorEquivalenceFlow) ->
              FormalCompilerInput
                (CompilerDatum.eventFlow route.bootstrapObligationFlow) ->
                CompleteSelfHostingEvidence
                  (SelfHostingClaimArtifact.certifiedRoute route)

theorem self_hosting_not_execution (runtime compilerDescription : EventFlow) :
    Not
      (CompleteSelfHostingEvidence
        (SelfHostingClaimArtifact.hostExecution runtime compilerDescription)) := by
  intro h
  cases h

structure P9CompilerEvidence where
  route : ProgrammaticSelfHostingRoute
  compilerIdentity :
    FormalCompilerInput
      (CompilerDatum.eventFlow route.compilerRecognitionFlow)
  compilerBehavior :
    FormalCompilerInput
      (CompilerDatum.eventFlow route.compilerCertificateFlow)
  selfCompilation :
    FormalCompilerInput
      (CompilerDatum.eventFlow route.selfCompilationFlow)
  behaviorEquivalence :
    FormalCompilerInput
      (CompilerDatum.eventFlow route.behaviorEquivalenceFlow)
  bootstrapObligations :
    FormalCompilerInput
      (CompilerDatum.eventFlow route.bootstrapObligationFlow)
  noHostLeakAudit : FormalCompilerInput (CompilerDatum.eventFlow route.recognizerVMFlow)
  globalVerificationStatus :
    FormalCompilerInput
      (CompilerDatum.eventFlow route.channelAndRecognizerRules)

inductive ProgrammaticP9Status : Type where
  | reached (evidence : P9CompilerEvidence)

theorem programmatic_realization_reaches_p9_with_evidence :
    ProgrammaticP9Status -> exists evidence : P9CompilerEvidence,
      CompleteSelfHostingEvidence
        (SelfHostingClaimArtifact.certifiedRoute evidence.route) := by
  intro status
  cases status with
  | reached evidence =>
      exact
        ⟨evidence,
          CompleteSelfHostingEvidence.certifiedRoute evidence.route
            evidence.compilerIdentity
            evidence.compilerBehavior
            evidence.selfCompilation
            evidence.behaviorEquivalence
            evidence.bootstrapObligations⟩

end BEDC.GroundCompiler.ProgrammaticRealization
