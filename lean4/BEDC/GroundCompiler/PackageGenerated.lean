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

end BEDC.GroundCompiler.PackageGenerated
