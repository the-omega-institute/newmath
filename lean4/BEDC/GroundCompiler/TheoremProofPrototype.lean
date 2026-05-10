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

theorem theorem_code_stronger_than_statement
    {T U : TheoremCandidateFlow} :
    TheoremCode T = TheoremCode U -> T = U := by
  intro hCode
  exact theorem_code_injective hCode

def StatementClassifierRelation : Type :=
  EventFlow -> EventFlow -> Prop

def AbstractPropositionClass
    (rel : StatementClassifierRelation) (Phi Psi : EventFlow) : Prop :=
  rel Phi Psi

def SameStatementClassifier (statement : EventFlow) :
    StatementClassifierRelation :=
  fun Phi Psi => Phi = statement /\ Psi = statement

theorem p7_singleton_theorem_flow (m : DisplayAlphabet) :
    TheoremFlow [[m]] := by
  refine
    ⟨[], ?_, ?_⟩
  · exact
      ⟨FormalCompilerInput.recognizedFlow [] [[m]],
        ⟨[m], [], rfl⟩⟩
  · refine
      ⟨[[m]], [[m]], [[m]], [[m]], [[m]], [[m]], [[m]], [[m]], ?_⟩
    exact
      ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
          ⟨[m], [], rfl⟩⟩,
        ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
            ⟨[m], [], rfl⟩⟩,
          ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
              ⟨[m], [], rfl⟩⟩,
            ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
                ⟨[m], [], rfl⟩⟩,
              ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
                  ⟨[m], [], rfl⟩⟩,
                ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
                    ⟨[m], [], rfl⟩⟩,
                  ⟨⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
                      ⟨[m], [], rfl⟩⟩,
                    ⟨⟨FormalCompilerInput.recognizedFlow [] [[m]], ⟨[m], [], rfl⟩⟩,
                      ⟨[m], [], rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem abstract_proposition_many_flows :
    exists rel : StatementClassifierRelation,
      exists R : P7GeneratedTheoremRecognizer,
        exists statement T U : TheoremCandidateFlow,
          Not (T = U) /\
            TheoremFlow T /\
            TheoremFlow U /\
            TheoremRoleSubflow R T statement TheoremRole.statement /\
            TheoremRoleSubflow R U statement TheoremRole.statement /\
            AbstractPropositionClass rel statement statement := by
  refine
    ⟨SameStatementClassifier [[BEDC.FKernel.Mark.BMark.b0]],
      [],
      [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b1]], ?_⟩
  exact
    ⟨(fun h => by cases h),
      p7_singleton_theorem_flow BEDC.FKernel.Mark.BMark.b0,
      p7_singleton_theorem_flow BEDC.FKernel.Mark.BMark.b1,
      ⟨⟨FormalCompilerInput.recognizedFlow [] [[BEDC.FKernel.Mark.BMark.b0]],
          ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩⟩,
        ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩⟩,
      ⟨⟨FormalCompilerInput.recognizedFlow [] [[BEDC.FKernel.Mark.BMark.b1]],
          ⟨[BEDC.FKernel.Mark.BMark.b1], [], rfl⟩⟩,
        ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩⟩,
      ⟨rfl, rfl⟩⟩

theorem abstract_proposition_not_theorem_code :
    exists rel : StatementClassifierRelation,
      exists R : P7GeneratedTheoremRecognizer,
        exists statement T U : TheoremCandidateFlow,
          TheoremFlow T /\
            TheoremFlow U /\
            TheoremRoleSubflow R T statement TheoremRole.statement /\
            TheoremRoleSubflow R U statement TheoremRole.statement /\
            AbstractPropositionClass rel statement statement /\
            Not (TheoremCode T = TheoremCode U) := by
  refine
    ⟨SameStatementClassifier [[BEDC.FKernel.Mark.BMark.b0]],
      [],
      [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b0]],
      [[BEDC.FKernel.Mark.BMark.b1]], ?_⟩
  exact
    ⟨p7_singleton_theorem_flow BEDC.FKernel.Mark.BMark.b0,
      p7_singleton_theorem_flow BEDC.FKernel.Mark.BMark.b1,
      ⟨⟨FormalCompilerInput.recognizedFlow [] [[BEDC.FKernel.Mark.BMark.b0]],
          ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩⟩,
        ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩⟩,
      ⟨⟨FormalCompilerInput.recognizedFlow [] [[BEDC.FKernel.Mark.BMark.b1]],
          ⟨[BEDC.FKernel.Mark.BMark.b1], [], rfl⟩⟩,
        ⟨[BEDC.FKernel.Mark.BMark.b0], [], rfl⟩⟩,
      ⟨rfl, rfl⟩,
      fun hCode => by
        have hFlow :
            [[BEDC.FKernel.Mark.BMark.b0]] =
              [[BEDC.FKernel.Mark.BMark.b1]] :=
          theorem_code_injective hCode
        cases hFlow⟩

def P7AcceptedTheoremFlow (T : TheoremCandidateFlow) : Prop :=
  AcceptedTheoremFlow T

def AcceptedTheoremCode (T : TheoremCandidateFlow) : List DisplayAlphabet :=
  TheoremCode T

theorem accepted_theorem_code_same_code {T : TheoremCandidateFlow} :
    P7AcceptedTheoremFlow T -> AcceptedTheoremCode T = TheoremCode T := by
  intro _
  rfl

theorem p7_singleton_nonempty (m : DisplayAlphabet) :
    NonemptyEventFlow [[m]] := by
  exact ⟨[m], [], rfl⟩

theorem p7_singleton_theorem_recognition (m : DisplayAlphabet) :
    TheoremRecognitionRelation [] [[m]] := by
  exact ⟨FormalCompilerInput.recognizedFlow [] [[m]], p7_singleton_nonempty m⟩

theorem p7_singleton_role_subflow (m : DisplayAlphabet)
    (role : TheoremRole) :
    TheoremRoleSubflow [] [[m]] [[m]] role := by
  exact ⟨p7_singleton_theorem_recognition m, p7_singleton_nonempty m⟩

theorem p7_singleton_complete_recognition (m : DisplayAlphabet) :
    CompleteTheoremFlowRecognition [] [[m]] := by
  refine ⟨[[m]], [[m]], [[m]], [[m]], [[m]], [[m]], [[m]], [[m]], ?_⟩
  exact
    ⟨p7_singleton_role_subflow m TheoremRole.statement,
      ⟨p7_singleton_role_subflow m TheoremRole.dependencies,
        ⟨p7_singleton_role_subflow m TheoremRole.proof,
          ⟨p7_singleton_role_subflow m TheoremRole.certificates,
            ⟨p7_singleton_role_subflow m TheoremRole.ledger,
              ⟨p7_singleton_role_subflow m TheoremRole.status,
                ⟨p7_singleton_role_subflow m TheoremRole.canonicalSite,
                  p7_singleton_role_subflow m TheoremRole.closingSeal⟩⟩⟩⟩⟩⟩⟩

theorem p7_singleton_proof_sound (m : DisplayAlphabet) :
    ProofSoundTheoremRecognition [] [[m]] := by
  refine
    ⟨[[m]], [[m]], [[m]], [[m]],
      p7_singleton_role_subflow m TheoremRole.statement,
      p7_singleton_role_subflow m TheoremRole.dependencies,
      p7_singleton_role_subflow m TheoremRole.proof, ?_⟩
  exact
    ⟨p7_singleton_nonempty m,
      p7_singleton_nonempty m,
      p7_singleton_nonempty m,
      p7_singleton_nonempty m⟩

theorem p7_singleton_certificate_sound (m : DisplayAlphabet) :
    CertificateSoundTheoremRecognition [] [[m]] := by
  exact
    ⟨[[m]], [], p7_singleton_role_subflow m TheoremRole.certificates,
      FormalCompilerInput.recognizedFlow [] [[m]]⟩

theorem p7_singleton_status_sound (m : DisplayAlphabet) :
    StatusSoundTheoremRecognition [] [[m]] := by
  exact
    ⟨[[m]], [], p7_singleton_role_subflow m TheoremRole.status,
      FormalCompilerInput.recognizedFlow [] [[m]]⟩

theorem p7_singleton_sound_theorem_flow (m : DisplayAlphabet) :
    SoundTheoremFlow [] [[m]] := by
  refine
    ⟨p7_singleton_complete_recognition m,
      p7_singleton_proof_sound m,
      p7_singleton_certificate_sound m, ?_, ?_, ?_⟩
  · exact ⟨[[m]], p7_singleton_role_subflow m TheoremRole.ledger⟩
  · exact p7_singleton_status_sound m
  · exact ⟨[[m]], p7_singleton_role_subflow m TheoremRole.canonicalSite⟩

theorem p7_singleton_accepted_theorem_flow (m : DisplayAlphabet) :
    P7AcceptedTheoremFlow [[m]] := by
  exact ⟨[], p7_singleton_sound_theorem_flow m⟩

def TheoremObjectMention (T O : EventFlow) : Prop :=
  TheoremSourceSubflow O T

theorem accepted_theorem_not_object_acceptance_distinct :
    exists T O : EventFlow,
      P7AcceptedTheoremFlow T /\
        TheoremObjectMention T O /\
        Not (AcceptedObjectFlow O) := by
  refine
    ⟨[[BEDC.FKernel.Mark.BMark.b0]], [],
      p7_singleton_accepted_theorem_flow BEDC.FKernel.Mark.BMark.b0, ?_,
      empty_not_accepted_object_flow⟩
  exact ⟨[], [[BEDC.FKernel.Mark.BMark.b0]], rfl⟩

theorem theorem_acceptance_and_object_acceptance_distinct :
    exists T O : EventFlow,
      P7AcceptedTheoremFlow T /\ Not (AcceptedObjectFlow O) := by
  cases accepted_theorem_not_object_acceptance_distinct with
  | intro T hT =>
      cases hT with
      | intro O hO =>
          exact ⟨T, O, hO.left, hO.right.right⟩

def P7BridgeWitnessFlow : EventFlow :=
  [[BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
    BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
    BEDC.FKernel.Mark.BMark.b0]]

def P7BridgeCertificateFlow (T : TheoremCandidateFlow) : Prop :=
  TheoremSourceSubflow P7BridgeWitnessFlow T

theorem singleton_not_p7_bridge_certificate :
    Not (P7BridgeCertificateFlow [[BEDC.FKernel.Mark.BMark.b0]]) := by
  intro h
  cases h with
  | intro before hAfter =>
      cases hAfter with
      | intro after hWhole =>
          cases before with
          | nil =>
              cases after with
              | nil =>
                  cases hWhole
              | cons a rest =>
                  cases hWhole
          | cons a rest =>
              cases rest with
              | nil =>
                  cases hWhole
              | cons b tail =>
                  cases hWhole

theorem p7_code_existence_still_not_bridge :
    exists T : TheoremCandidateFlow,
      P7AcceptedTheoremFlow T /\
        LegalTheoremCode (AcceptedTheoremCode T) /\
        Not (P7BridgeCertificateFlow T) := by
  exact
    ⟨[[BEDC.FKernel.Mark.BMark.b0]],
      p7_singleton_accepted_theorem_flow BEDC.FKernel.Mark.BMark.b0,
      ⟨[[BEDC.FKernel.Mark.BMark.b0]], rfl⟩,
      singleton_not_p7_bridge_certificate⟩

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

def SoundP7Report (report : P7Output) : Prop :=
  (forall T : TheoremCandidateFlow,
    forall c : List DisplayAlphabet,
      List.Mem (P7ReportDatum.theoremCode T c) report ->
        exists R : P7GeneratedTheoremRecognizer,
          P7SoundTheoremFlow R T /\ c = TheoremCode T) /\
    (forall T : TheoremCandidateFlow,
      List.Mem (P7ReportDatum.acceptedTheorem T) report ->
        P7AcceptedTheoremFlow T)

theorem sound_p7_report_theorem {report : P7Output} :
    SoundP7Report report ->
      (forall T : TheoremCandidateFlow,
        forall c : List DisplayAlphabet,
          List.Mem (P7ReportDatum.theoremCode T c) report ->
            exists R : P7GeneratedTheoremRecognizer,
              P7SoundTheoremFlow R T /\ c = TheoremCode T) /\
        (forall T : TheoremCandidateFlow,
          forall c : List DisplayAlphabet,
            List.Mem (P7ReportDatum.theoremCode T c) report ->
              List.Mem (P7ReportDatum.acceptedTheorem T) report ->
                P7AcceptedTheoremFlow T /\ c = AcceptedTheoremCode T) := by
  intro hSound
  constructor
  · exact hSound.left
  · intro T c hCode hAccepted
    constructor
    · exact hSound.right T hAccepted
    · cases hSound.left T c hCode with
      | intro _ hWitness =>
          exact hWitness.right

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
