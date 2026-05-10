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

theorem no_package_without_ledger {S : PackageCandidateFlow} :
    PkgFlow S ->
      exists R : GeneratedPackageRecognizer,
        exists L : PackageCandidateFlow,
          PackageRecognitionRelation R S /\ PackageLedgerSubflow R S L := by
  intro hPkg
  cases hPkg with
  | intro R hRecognizes =>
      have hLedger : PackageLedgerSubflow R S S := by
        change PackageRecognitionRelation R S /\ NonemptyEventFlow S
        exact ⟨hRecognizes, hRecognizes.right⟩
      exact ⟨R, S, hRecognizes, hLedger⟩

theorem visible_code_insufficient {S : PackageCandidateFlow} :
    Not
      (exists R : GeneratedPackageRecognizer,
        exists L : PackageCandidateFlow,
          PackageRecognitionRelation R S /\ PackageLedgerSubflow R S L) ->
      Not (PkgFlow S) := by
  intro hNoLedger hPkg
  exact hNoLedger (no_package_without_ledger hPkg)

theorem package_not_merely_visible_token {S : PackageCandidateFlow} :
    PkgFlow S ->
      exists R : GeneratedPackageRecognizer,
        exists L : PackageCandidateFlow,
          PackageRecognitionRelation R S /\ PackageLedgerSubflow R S L :=
  no_package_without_ledger

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

theorem raw_flows_code_bijective {S T : PackageCandidateFlow} :
    PackageCode S = PackageCode T <-> S = T := by
  simpa [PackageCode, PackageCodeEquiv] using
    (package_code_equivalence_is_equality : PackageCodeEquiv S T <-> S = T)

def PackageClassifierRelation : Type :=
  PackageCandidateFlow -> PackageCandidateFlow -> Prop

def PackageClassifierQuotient
    (rel : PackageClassifierRelation) (S T : PackageCandidateFlow) : Prop :=
  rel S T

def ClassifierCollapsesDistinctCode (rel : PackageClassifierRelation) : Prop :=
  exists S T : PackageCandidateFlow,
    PkgFlow S /\
      PkgFlow T /\
      Not (PackageCode S = PackageCode T) /\
      PackageClassifierQuotient rel S T

theorem classified_not_code_bijective {rel : PackageClassifierRelation} :
    (exists S T : PackageCandidateFlow,
      PkgFlow S /\
        PkgFlow T /\
        Not (S = T) /\
        PackageClassifierQuotient rel S T) ->
      ClassifierCollapsesDistinctCode rel := by
  intro h
  cases h with
  | intro S hS =>
      cases hS with
      | intro T hT =>
          refine ⟨S, T, hT.left, hT.right.left, ?_, hT.right.right.right⟩
          intro hCode
          have hEq : S = T :=
            (raw_flows_code_bijective (S := S) (T := T)).mp hCode
          exact hT.right.right.left hEq

theorem raw_code_vs_classified_object_layers {rel : PackageClassifierRelation} :
    (forall S T : PackageCandidateFlow, PackageCode S = PackageCode T -> S = T) /\
      ((exists S T : PackageCandidateFlow,
        PkgFlow S /\
          PkgFlow T /\
          Not (S = T) /\
          PackageClassifierQuotient rel S T) ->
        ClassifierCollapsesDistinctCode rel) := by
  constructor
  · intro S T hCode
    exact (raw_flows_code_bijective (S := S) (T := T)).mp hCode
  · intro h
    exact classified_not_code_bijective h

def RecognizesPkgCode
    (R : GeneratedPackageRecognizer) (c : List DisplayAlphabet) : Prop :=
  exists S : PackageCandidateFlow,
    Decode c = some S /\ PackageRecognitionRelation R S

theorem package_code_recognition_has_decoded_flow
    {R : GeneratedPackageRecognizer} {c : List DisplayAlphabet} :
    RecognizesPkgCode R c ->
      exists S : PackageCandidateFlow,
        Decode c = some S /\ PackageRecognitionRelation R S := by
  intro h
  exact h

theorem package_recognition_conservativity
    {R : GeneratedPackageRecognizer} {S : PackageCandidateFlow}
    {w : RawEvent} {m : DisplayAlphabet} :
    PackageRecognitionRelation R S ->
      List.Mem w S -> List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  intro _ hEvent hMark
  exact event_flow_conservativity hEvent hMark

def DerivedInterfaceLicense (S : PackageCandidateFlow) : Prop :=
  exists R : GeneratedPackageRecognizer,
    exists N C : EventFlow,
      PackageRecognitionRelation R S /\
        RecognizedNameCertFlow N /\
        RecognizedClosureCertFlow C /\
        AcceptedObjectFlow S

theorem recognized_package_weaker_than_derived_interface {S : PackageCandidateFlow} :
    DerivedInterfaceLicense S -> PkgFlow S := by
  intro h
  cases h with
  | intro R hR =>
      cases hR with
      | intro _ hN =>
          cases hN with
          | intro _ hC =>
              exact ⟨R, hC.left⟩

end BEDC.GroundCompiler.PackageGenerated
