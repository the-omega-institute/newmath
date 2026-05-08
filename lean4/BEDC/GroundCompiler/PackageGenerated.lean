import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.PackageGenerated

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

def PackageCandidateFlow : Type :=
  EventFlow

def GeneratedPackageRecognizer : Type :=
  GeneratedRecognizer

def PackageRecognitionRelation
    (R : GeneratedPackageRecognizer) (S : PackageCandidateFlow) : Prop :=
  RecognizesPkg R S

def PkgFlow (S : PackageCandidateFlow) : Prop :=
  exists R : GeneratedPackageRecognizer, PackageRecognitionRelation R S

def PackageCode (S : PackageCandidateFlow) : List DisplayAlphabet :=
  FlowEncoding S

theorem package_recognition_preserves_code
    {R : GeneratedPackageRecognizer} {S : PackageCandidateFlow} :
    PackageRecognitionRelation R S -> PackageCode S = FlowEncoding S := by
  intro _
  rfl

theorem package_code_not_separate {S : PackageCandidateFlow} :
    PkgFlow S -> PackageCode S = FlowEncoding S := by
  intro _
  rfl

inductive PackageRole : Type where
  | source
  | pattern
  | classifier
  | stability
  | ledger
  | seal

def PackageRoleEmergence
    (R : GeneratedPackageRecognizer) (S T : PackageCandidateFlow)
    (_rho : PackageRole) : Prop :=
  PackageRecognitionRelation R S /\ NonemptyEventFlow T

def PackageSealSubflow
    (R : GeneratedPackageRecognizer) (S sigma : PackageCandidateFlow) : Prop :=
  PackageRoleEmergence R S sigma PackageRole.seal

def PackageLedgerSubflow
    (R : GeneratedPackageRecognizer) (S L : PackageCandidateFlow) : Prop :=
  PackageRoleEmergence R S L PackageRole.ledger

theorem package_seal_is_source_subflow
    {R : GeneratedPackageRecognizer} {S sigma : PackageCandidateFlow} :
    PackageSealSubflow R S sigma -> NonemptyEventFlow sigma := by
  intro hSeal
  exact hSeal.right

theorem no_external_package_input :
    Not (FormalCompilerInput CompilerDatum.hostPkg) :=
  structural_hidden_not_formal StructuralHiddenInput.hostPkg

def RecognitionPreservingCompilation : Prop :=
  forall R : GeneratedPackageRecognizer,
    forall S : PackageCandidateFlow,
      PackageRecognitionRelation R S ->
        exists S' : PackageCandidateFlow,
          Decode (FlowEncoding S) = some S' /\
            PackageRecognitionRelation R S'

theorem channel_compilation_preserves_recognition :
    RecognitionPreservingCompilation := by
  intro R S hRecognizes
  exact ⟨S, flow_level_round_trip S, hRecognizes⟩

theorem package_recognition_invariant {S : PackageCandidateFlow} :
    PkgFlow S ->
      exists S' : PackageCandidateFlow,
        Decode (FlowEncoding S) = some S' /\ PkgFlow S' := by
  intro hPkg
  cases hPkg with
  | intro R hRecognizes =>
      exact ⟨S, flow_level_round_trip S, ⟨R, hRecognizes⟩⟩

def PackageCodeEquiv (S T : PackageCandidateFlow) : Prop :=
  FlowEncoding S = FlowEncoding T

theorem package_code_equivalence_is_equality {S T : PackageCandidateFlow} :
    PackageCodeEquiv S T <-> S = T := by
  constructor
  · intro hCode
    have hDecode : Decode (FlowEncoding S) = Decode (FlowEncoding T) := by
      rw [hCode]
    rw [flow_level_round_trip S, flow_level_round_trip T] at hDecode
    cases hDecode
    rfl
  · intro hEq
    cases hEq
    rfl

end BEDC.GroundCompiler.PackageGenerated
