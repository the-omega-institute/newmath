import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.DerivCertGenerated
import BEDC.GroundCompiler.TheoremGenerated
import BEDC.GroundCompiler.ChapterFlow

namespace BEDC.GroundCompiler.RecognizerFlows

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.DerivCertGenerated
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.TheoremGenerated
open BEDC.GroundCompiler.ChapterFlow

def RecognizerCertCandidateFlow : Type :=
  EventFlow

def RecognizesRecognizerCert
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  NonemptyEventFlow C_R /\
    FormalCompilerInput (CompilerDatum.recognizedFlow Q C_R) /\
    FormalCompilerInput (CompilerDatum.recognizedFlow R rho)

def CertifiedRecognizer
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  exists C_R : RecognizerCertCandidateFlow,
    exists Q : GeneratedRecognizer,
      RecognizesRecognizerCert Q C_R R rho

def RecognizerCertificateField
    (Q : GeneratedRecognizer) (_C_R : RecognizerCertCandidateFlow)
    (X : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow Q X)

def RecognizerCertificateFields
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (D T rho snd cmp ledger failure stability recSeal : EventFlow) : Prop :=
  RecognizerCertificateField Q C_R D /\
    RecognizerCertificateField Q C_R T /\
    RecognizerCertificateField Q C_R rho /\
    RecognizerCertificateField Q C_R snd /\
    RecognizerCertificateField Q C_R cmp /\
    RecognizerCertificateField Q C_R ledger /\
    RecognizerCertificateField Q C_R failure /\
    RecognizerCertificateField Q C_R stability /\
    RecognizerCertificateField Q C_R recSeal

def RoleOK (rho : RecognitionRole) (S : EventFlow) : Prop :=
  NonemptyEventFlow rho /\
    FormalCompilerInput (CompilerDatum.recognizedFlow rho S)

def RecSound (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  forall S : EventFlow, Recognizes R rho S -> RoleOK rho S

def RecComplete
    (R : RecognizerCandidateFlow) (D : EventFlow) (rho : RecognitionRole) :
    Prop :=
  NonemptyEventFlow D /\
    forall S : EventFlow,
      FormalCompilerInput (CompilerDatum.recognizedFlow D S) ->
        RoleOK rho S -> Recognizes R rho S

def RecFailureLedger
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (F : EventFlow) : Prop :=
  RecognizerCertificateField Q C_R F /\ NonemptyEventFlow F

def RecLedger
    (Q : GeneratedRecognizer) (C_R : RecognizerCertCandidateFlow)
    (L : EventFlow) : Prop :=
  RecognizerCertificateField Q C_R L /\ NonemptyEventFlow L

def RecognizerConservative
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  forall S : EventFlow,
    Recognizes R rho S ->
      forall w : RawEvent,
        List.Mem w S ->
          forall m : DisplayAlphabet,
            List.Mem m w -> m = BMark.b0 \/ m = BMark.b1

def RecognizerHierarchy : Type :=
  List (RecognizerCandidateFlow × RecognitionRole)

def RecognizesLegalZStream
    (_R0 : RecognizerCandidateFlow) (c : List DisplayAlphabet) : Prop :=
  LegalZStream c /\
    exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c

def RecognizesEventFlow
    (_R0 : RecognizerCandidateFlow) (S : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow S)

def BootstrapBaseRecognizer (R0 : RecognizerCandidateFlow) : Prop :=
  (forall c : List DisplayAlphabet,
    LegalZStream c -> RecognizesLegalZStream R0 c) /\
    (forall S : EventFlow, RecognizesEventFlow R0 S)

def FormalRecognitionEvidence
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) (S : EventFlow) :
    Prop :=
  CertifiedRecognizer R rho /\ Recognizes R rho S

def PackageRecognizerLevel
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  CertifiedRecognizer R rho /\
    forall S : EventFlow,
      RecognizesPkg R S -> FormalRecognitionEvidence R rho S

def CertificateRecognizerLevel
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  CertifiedRecognizer R rho /\
    (forall S : EventFlow,
      RecognizesNameCert R S -> FormalRecognitionEvidence R rho S) /\
    (forall D N s : EventFlow,
      DerivCertFlow D N s -> FormalRecognitionEvidence R rho D) /\
    (forall A N s : EventFlow,
      AcceptedFlow A N s -> FormalRecognitionEvidence R rho A)

def TheoremRecognizerLevel
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  CertifiedRecognizer R rho /\
    forall T : TheoremCandidateFlow,
      TheoremRecognitionRelation R T -> FormalRecognitionEvidence R rho T

def ChapterRecognizerLevel
    (R : RecognizerCandidateFlow) (rho : RecognitionRole) : Prop :=
  CertifiedRecognizer R rho /\
    forall C : ChapterCandidateFlow,
      RecognizesChapter R C -> FormalRecognitionEvidence R rho C

def RecognizerSelfDescriptionFlow
    (R : RecognizerCandidateFlow) (D_R : EventFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow D_R) /\
    exists rho : RecognitionRole, FormalRecognitionEvidence R rho D_R

def CompilerRecognizerFlow (C : EventFlow) : Prop :=
  RecognizedCompilerFlow C

def CompilerBehaviorClassifier (C C' : EventFlow) : Prop :=
  exists behavior : CompilerBehavior, behavior C C' /\ behavior C' C

def CompilesCompilerFlow (C S T : EventFlow) : Prop :=
  CompilerRecognizerFlow C /\
    FormalCompilerInput (CompilerDatum.eventFlow S) /\
    FormalCompilerInput (CompilerDatum.eventFlow T)

def SelfHostingCompilerFlow (C : EventFlow) : Prop :=
  CompilerRecognizerFlow C /\
    exists C' : EventFlow,
      CompilesCompilerFlow C C C' /\ CompilerBehaviorClassifier C' C

def BootstrapObligation : Type :=
  EventFlow

def UndischargedBootstrapObligation (O : BootstrapObligation) : Prop :=
  NonemptyEventFlow O

def FullNoHiddenInputSelfHosting (C : EventFlow) : Prop :=
  SelfHostingCompilerFlow C /\
    forall O : BootstrapObligation, Not (UndischargedBootstrapObligation O)

theorem formal_recognition_evidence_requires_certified
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    FormalRecognitionEvidence R rho S -> CertifiedRecognizer R rho := by
  intro h
  exact h.left

theorem uncertified_cannot_license
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    Not (CertifiedRecognizer R rho) ->
      Not (FormalRecognitionEvidence R rho S) := by
  intro hNotCert hEvidence
  exact hNotCert (formal_recognition_evidence_requires_certified hEvidence)

theorem bootstrap_base_no_math_structure {R0 : RecognizerCandidateFlow} :
    BootstrapBaseRecognizer R0 ->
      Not (FormalCompilerInput CompilerDatum.hostPkg) /\
        Not (FormalCompilerInput CompilerDatum.hostNameCert) /\
        Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
        Not (AcceptedObjectFlow []) := by
  intro _
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostNameCert
    · constructor
      · exact
          structural_hidden_not_formal
            StructuralHiddenInput.hostTheoremIdentifier
      · exact empty_not_accepted_object_flow

theorem certified_recognition_only
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} :
    CertifiedRecognizer R rho ->
      RecognizerConservative R rho ->
        forall S : EventFlow,
          Recognizes R rho S ->
            forall w : RawEvent,
              List.Mem w S ->
                forall m : DisplayAlphabet,
                  List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro _ hCons
  exact hCons

theorem recognizer_hierarchy_removes_hidden_input
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow} :
    FormalRecognitionEvidence R rho S ->
      Not (StructuralHiddenInput (CompilerDatum.recognizedFlow R S)) := by
  intro _ hHidden
  cases hHidden

theorem host_parser_output_inadmissible :
    Not (FormalCompilerInput CompilerDatum.hostParserState) :=
  structural_hidden_not_formal StructuralHiddenInput.hostParserState

theorem external_views_inadmissible :
    Not (FormalCompilerInput CompilerDatum.hostYAML) /\
      Not (FormalCompilerInput CompilerDatum.hostAST) /\
      Not (FormalCompilerInput CompilerDatum.hostTheoremIdentifier) /\
      Not (FormalCompilerInput CompilerDatum.hostPkg) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostYAML
  · constructor
    · exact structural_hidden_not_formal StructuralHiddenInput.hostAST
    · constructor
      · exact
          structural_hidden_not_formal
            StructuralHiddenInput.hostTheoremIdentifier
      · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg

theorem self_hosting_projects_behavior_classifier {C : EventFlow} :
    SelfHostingCompilerFlow C ->
      exists C' : EventFlow,
        CompilesCompilerFlow C C C' /\ CompilerBehaviorClassifier C' C := by
  intro h
  exact h.right

theorem self_hosting_removes_compiler_as_hidden_input {C : EventFlow} :
    SelfHostingCompilerFlow C ->
      CompilerRecognizerFlow C /\
        FormalCompilerInput (CompilerDatum.eventFlow C) := by
  intro h
  exact ⟨h.left, h.left⟩

theorem full_no_hidden_input_needs_self_hosting {C : EventFlow} :
    Not (SelfHostingCompilerFlow C) ->
      Not (FullNoHiddenInputSelfHosting C) := by
  intro hNoSelf hFull
  exact hNoSelf hFull.left

theorem bootstrap_obligation_blocks_full_self_hosting_claim
    {C : EventFlow} {O : BootstrapObligation} :
    UndischargedBootstrapObligation O ->
      Not (FullNoHiddenInputSelfHosting C) := by
  intro hObligation hFull
  exact (hFull.right O) hObligation

theorem recognizer_flows_conservative_over_kernel
    {R : RecognizerCandidateFlow} {rho : RecognitionRole} {S : EventFlow}
    {w : RawEvent} {m : DisplayAlphabet} :
    Recognizes R rho S ->
      List.Mem w S -> List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro _ _ _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

theorem recognition_not_acceptance :
    Not (forall R : RecognizerCandidateFlow,
      forall rho : RecognitionRole,
        forall S : EventFlow, Recognizes R rho S -> AcceptedObjectFlow S) := by
  intro h
  have hAccepted :
      AcceptedObjectFlow [] :=
    h [] [] [] (FormalCompilerInput.recognizedFlow [] [])
  exact empty_not_accepted_object_flow hAccepted

end BEDC.GroundCompiler.RecognizerFlows
