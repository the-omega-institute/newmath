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

theorem nonempty_not_source_subflow_empty {Pi : EventFlow} :
    NonemptyEventFlow Pi -> Not (TheoremSourceSubflow Pi []) := by
  intro hNonempty hSource
  cases hNonempty with
  | intro w hRest =>
      cases hRest with
      | intro rest hPi =>
          cases hSource with
          | intro before hAfter =>
              cases hAfter with
              | intro after hWhole =>
                  cases hPi
                  cases before <;> cases hWhole

theorem empty_not_recognized_proof_flow
    {R : GeneratedProofFlowRecognizer} {Pi : EventFlow} :
    Not (RecognizedProofFlow R [] Pi) := by
  intro h
  exact nonempty_not_source_subflow_empty h.right.left h.left

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

theorem code_not_proof_flow :
    exists c : List DisplayAlphabet,
      exists S : EventFlow,
        Decode c = some S /\
          (forall RPi : GeneratedProofFlowRecognizer,
            forall Pi : EventFlow, Not (RecognizedProofFlow RPi S Pi)) := by
  exact ⟨[], [], rfl, fun _ _ hProof => empty_not_recognized_proof_flow hProof⟩

theorem proof_flow_not_checking :
    exists RPi : GeneratedProofFlowRecognizer,
      exists S Pi Phi Ddep : EventFlow,
        RecognizedProofFlow RPi S Pi /\
          (forall Rchk : GeneratedProofChecker,
            Not (ProofSoundness Rchk Phi Ddep Pi)) := by
  refine
    ⟨[], [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b0]], [], [], ?_⟩
  constructor
  · constructor
    · exact ⟨[], [], rfl⟩
    · constructor
      · exact ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩
      · exact FormalCompilerInput.recognizedFlow []
          [[BEDC.FKernel.Mark.BMark.b0]]
  · intro _ hCheck
    exact empty_not_nonempty_event_flow hCheck.right.left

def TheoremCandidate (S T : EventFlow) : Prop :=
  TheoremSourceSubflow T S

def P7GeneratedTheoremRecognizer : Type :=
  GeneratedTheoremRecognizer

def P7TheoremSubflows
    (R : P7GeneratedTheoremRecognizer) (T statement dependencies proof
      certificates ledger status canonicalSite sealFlow : EventFlow) : Prop :=
  TheoremRoleSubflow R T statement TheoremRole.statement /\
    TheoremRoleSubflow R T dependencies TheoremRole.dependencies /\
    TheoremRoleSubflow R T proof TheoremRole.proof /\
    TheoremRoleSubflow R T certificates TheoremRole.certificates /\
    TheoremRoleSubflow R T ledger TheoremRole.ledger /\
    TheoremRoleSubflow R T status TheoremRole.status /\
    TheoremRoleSubflow R T canonicalSite TheoremRole.canonicalSite /\
    TheoremRoleSubflow R T sealFlow TheoremRole.closingSeal

def P7CompleteTheoremRecognition
    (R : P7GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  exists statement dependencies proof certificates ledger status canonicalSite
      sealFlow : EventFlow,
    P7TheoremSubflows R T statement dependencies proof certificates ledger
      status canonicalSite sealFlow

def P7TheoremSoundnessComponents
    (R : P7GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  ProofSoundTheoremRecognition R T /\
    CertificateSoundTheoremRecognition R T /\
    LedgerSoundTheoremRecognition R T /\
    StatusSoundTheoremRecognition R T /\
    SiteSoundTheoremRecognition R T

def P7SoundTheoremFlow
    (R : P7GeneratedTheoremRecognizer) (T : TheoremCandidateFlow) : Prop :=
  P7CompleteTheoremRecognition R T /\ P7TheoremSoundnessComponents R T

theorem complete_theorem_recognition_to_p7
    {R : P7GeneratedTheoremRecognizer} {T : TheoremCandidateFlow} :
    CompleteTheoremFlowRecognition R T -> P7CompleteTheoremRecognition R T := by
  intro h
  cases h with
  | intro statement hStatement =>
      cases hStatement with
      | intro dependencies hDependencies =>
          cases hDependencies with
          | intro proof hProof =>
              cases hProof with
              | intro certificates hCertificates =>
                  cases hCertificates with
                  | intro ledger hLedger =>
                      cases hLedger with
                      | intro status hStatus =>
                          cases hStatus with
                          | intro canonicalSite hSite =>
                              cases hSite with
                              | intro sealFlow hSubflows =>
                                  exact
                                    ⟨statement, dependencies, proof,
                                      certificates, ledger, status,
                                      canonicalSite, sealFlow, hSubflows⟩

theorem no_theorem_without_eight_subflows
    {T : TheoremCandidateFlow} :
    TheoremFlow T ->
      exists R : P7GeneratedTheoremRecognizer,
        TheoremRecognitionRelation R T /\ P7CompleteTheoremRecognition R T := by
  intro h
  cases h with
  | intro R hR =>
      exact ⟨R, hR.left, complete_theorem_recognition_to_p7 hR.right⟩

theorem p7_incomplete_theorem_candidate_not_theorem
    {S T : EventFlow} :
    TheoremCandidate S T ->
      (forall R : P7GeneratedTheoremRecognizer,
        TheoremRecognitionRelation R T ->
          Not (P7CompleteTheoremRecognition R T)) ->
        Not (TheoremFlow T) := by
  intro _ hIncomplete hFlow
  cases hFlow with
  | intro R hRecognized =>
      exact
        hIncomplete R hRecognized.left
          (complete_theorem_recognition_to_p7 hRecognized.right)

theorem sound_theorem_flow_establishes_theorem_code
    {R : P7GeneratedTheoremRecognizer} {T : TheoremCandidateFlow} :
    P7SoundTheoremFlow R T ->
      TheoremCode T = FlowEncoding T /\ Decode (TheoremCode T) = some T := by
  intro _
  constructor
  · rfl
  · exact theorem_code_round_trip T

theorem p7_theorem_code_injective
    {RT RU : P7GeneratedTheoremRecognizer} {T U : TheoremCandidateFlow} :
    P7SoundTheoremFlow RT T ->
      P7SoundTheoremFlow RU U ->
        TheoremCode T = TheoremCode U -> T = U := by
  intro _ _ hCode
  exact theorem_code_injective hCode

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
