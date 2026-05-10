import BEDC.GroundCompiler.DerivCertGenerated
import BEDC.GroundCompiler.TheoremGenerated

namespace BEDC.GroundCompiler.TheoremProofPrototype

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.DerivCertGenerated
open BEDC.GroundCompiler.TheoremGenerated

inductive P7FormalInput : Type where
  | channel (c : List DisplayAlphabet) (h : LegalZStream c)
  | eventFlow (S : EventFlow)

inductive P7ExternalInput : Type where
  | theoremObject
  | proofObject

inductive P7InputRepresentation : Type where
  | formal (x : P7FormalInput)
  | external (x : P7ExternalInput)

theorem theorem_proof_objects_not_formal :
    (forall x : P7FormalInput,
      Not (P7InputRepresentation.external P7ExternalInput.theoremObject =
        P7InputRepresentation.formal x)) /\
      (forall x : P7FormalInput,
        Not (P7InputRepresentation.external P7ExternalInput.proofObject =
          P7InputRepresentation.formal x)) := by
  constructor
  · intro x h
    cases h
  · intro x h
    cases h

def StatementCandidate (S Phi : EventFlow) : Prop :=
  TheoremSourceSubflow Phi S

def GeneratedStatementRecognizer : Type :=
  GeneratedRecognizer

def RecognizesStatement
    (R : GeneratedStatementRecognizer) (S Phi : EventFlow) : Prop :=
  StatementCandidate S Phi /\
    NonemptyEventFlow Phi /\
    Recognizes R S Phi

def RecognizedStatementFlow
    (R : GeneratedStatementRecognizer) (S Phi : EventFlow) : Prop :=
  RecognizesStatement R S Phi

def DependencyCandidate (S D : EventFlow) : Prop :=
  TheoremSourceSubflow D S

def GeneratedDependencyRecognizer : Type :=
  GeneratedRecognizer

def RecognizesDependencies
    (R : GeneratedDependencyRecognizer) (S D : EventFlow) : Prop :=
  DependencyCandidate S D /\
    NonemptyEventFlow D /\
    Recognizes R S D

def RecognizedDependencyFlow
    (R : GeneratedDependencyRecognizer) (S D : EventFlow) : Prop :=
  RecognizesDependencies R S D

inductive DependencyStatus : Type where
  | earlierGenerated
  | earlierTheorem
  | earlierCertificate
  | localTheorem
  | deferredObligation
  | cannotClaim
  | openObligation
  | futureUngenerated

def DependencyStatusSound (status : DependencyStatus) : Prop :=
  Not (status = DependencyStatus.futureUngenerated)

def DependencySoundness
    (D : EventFlow) (statusOf : RawEvent -> DependencyStatus) : Prop :=
  forall dep : RawEvent, List.Mem dep D -> DependencyStatusSound (statusOf dep)

def SoundTheoremWithDependencies
    (R : GeneratedTheoremRecognizer) (T D : TheoremCandidateFlow)
    (statusOf : RawEvent -> DependencyStatus) : Prop :=
  TheoremRoleSubflow R T D TheoremRole.dependencies /\
    DependencySoundness D statusOf

theorem future_ungenerated_dependency_unsound
    {D : EventFlow} {statusOf : RawEvent -> DependencyStatus}
    {dep : RawEvent} :
    List.Mem dep D ->
      statusOf dep = DependencyStatus.futureUngenerated ->
        Not (DependencySoundness D statusOf) := by
  intro hMem hStatus hSound
  exact hSound dep hMem hStatus

theorem unsound_dependency_blocks_theorem_recognition
    {R : GeneratedTheoremRecognizer} {T D : TheoremCandidateFlow}
    {statusOf : RawEvent -> DependencyStatus} :
    TheoremRoleSubflow R T D TheoremRole.dependencies ->
      Not (DependencySoundness D statusOf) ->
        Not (SoundTheoremWithDependencies R T D statusOf) := by
  intro _ hUnsound hSound
  exact hUnsound hSound.right

def ProofCandidate (S Pi : EventFlow) : Prop :=
  TheoremSourceSubflow Pi S

def GeneratedProofFlowRecognizer : Type :=
  GeneratedRecognizer

def RecognizesProofFlow
    (R : GeneratedProofFlowRecognizer) (S Pi : EventFlow) : Prop :=
  ProofCandidate S Pi /\
    NonemptyEventFlow Pi /\
    Recognizes R S Pi

def RecognizedProofFlow
    (R : GeneratedProofFlowRecognizer) (S Pi : EventFlow) : Prop :=
  RecognizesProofFlow R S Pi

def GeneratedProofChecker : Type :=
  GeneratedProofCheckerFlow

def ProofSoundness
    (Rchk : GeneratedProofChecker) (Phi Ddep Pi : EventFlow) : Prop :=
  ChecksProof Rchk Phi Ddep Pi

def ProofUsableAsTheoremProof
    (S Phi Ddep Pi : EventFlow) : Prop :=
  exists RPi : GeneratedProofFlowRecognizer,
    exists Rchk : GeneratedProofChecker,
      RecognizedProofFlow RPi S Pi /\ ProofSoundness Rchk Phi Ddep Pi

theorem proof_candidate_alone_insufficient
    {S Phi Ddep Pi : EventFlow} :
    ProofCandidate S Pi ->
      (forall RPi : GeneratedProofFlowRecognizer,
        Not (RecognizedProofFlow RPi S Pi)) ->
      (forall Rchk : GeneratedProofChecker,
        Not (ProofSoundness Rchk Phi Ddep Pi)) ->
      Not (ProofUsableAsTheoremProof S Phi Ddep Pi) := by
  intro _ hNoRecognized _ hUsable
  cases hUsable with
  | intro RPi hChecker =>
      cases hChecker with
      | intro _ hPair =>
          exact hNoRecognized RPi hPair.left

inductive P7ReportDatum : Type where
  | decodedEventFlow (S : EventFlow)
  | statementCandidate (S Phi : EventFlow)
  | recognizedStatement
      (R : GeneratedStatementRecognizer) (S Phi : EventFlow)
  | dependencyCandidate (S D : EventFlow)
  | recognizedDependency (R S D : EventFlow)
  | proofCandidate (S Pi : EventFlow)
  | recognizedProof (R S Pi : EventFlow)
  | proofCheckingResult
      (checker statement dependencies proof : EventFlow)
  | theoremCandidate (T : TheoremCandidateFlow)
  | recognizedTheorem (R : GeneratedTheoremRecognizer) (T : TheoremCandidateFlow)
  | theoremCode (T : TheoremCandidateFlow) (c : List DisplayAlphabet)
  | acceptedTheorem (T : TheoremCandidateFlow)
  | missingField (candidate : EventFlow)
  | proofFailure (candidate : EventFlow)
  | certificateFailure (candidate : EventFlow)
  | ledgerFailure (candidate : EventFlow)
  | statusFailure (candidate : EventFlow)
  | canonicalSiteFailure (candidate : EventFlow)
  | warning (datum : EventFlow)
  | cannotClaim (datum : EventFlow)

def P7Output : Type :=
  List P7ReportDatum

structure TheoremProofPrototype where
  p6 : DerivAcceptPrototype
  run : P7FormalInput -> P7Output
  theoremObjectsNotFormal :
    (forall x : P7FormalInput,
      Not (P7InputRepresentation.external P7ExternalInput.theoremObject =
        P7InputRepresentation.formal x))
  proofObjectsNotFormal :
    (forall x : P7FormalInput,
      Not (P7InputRepresentation.external P7ExternalInput.proofObject =
        P7InputRepresentation.formal x))
  statementRecognitionBacked :
    forall {R : GeneratedStatementRecognizer} {S Phi : EventFlow},
      List.Mem (P7ReportDatum.recognizedStatement R S Phi)
          (run (P7FormalInput.eventFlow S)) ->
        RecognizesStatement R S Phi
  theoremRecognitionBacked :
    forall {R : GeneratedTheoremRecognizer} {T : TheoremCandidateFlow}
      {S : EventFlow},
      List.Mem (P7ReportDatum.recognizedTheorem R T)
          (run (P7FormalInput.eventFlow S)) ->
        TheoremRecognitionRelation R T
  theoremCodeMediated :
    forall {T : TheoremCandidateFlow} {c : List DisplayAlphabet} {S : EventFlow},
      List.Mem (P7ReportDatum.theoremCode T c) (run (P7FormalInput.eventFlow S)) ->
        c = TheoremCode T

end BEDC.GroundCompiler.TheoremProofPrototype
