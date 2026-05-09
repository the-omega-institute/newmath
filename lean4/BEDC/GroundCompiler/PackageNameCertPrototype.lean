import BEDC.GroundCompiler.ChannelEncoding
import BEDC.GroundCompiler.NameCertGenerated

namespace BEDC.GroundCompiler.PackageNameCertPrototype

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding

inductive P5FormalInput : Type where
  | channel (c : List DisplayAlphabet) (h : LegalZStream c)
  | eventFlow (S : EventFlow)

theorem p5_channel_input_decodes {c : List DisplayAlphabet} :
    LegalZStream c -> exists S : EventFlow, Decode c = some S := by
  intro hLegal
  cases hLegal with
  | intro S hS =>
      exact ⟨S, by rw [hS]; exact flow_level_round_trip S⟩

theorem p5_no_package_object_input :
    Not (FormalCompilerInput CompilerDatum.hostPkg) /\
      Not (FormalCompilerInput CompilerDatum.hostNameCert) := by
  constructor
  · exact structural_hidden_not_formal StructuralHiddenInput.hostPkg
  · exact structural_hidden_not_formal StructuralHiddenInput.hostNameCert

def PackageCandidate (S P : EventFlow) : Prop :=
  BEDC.GroundCompiler.NameCertGenerated.SourceSubflow P S

theorem package_candidate_has_ambient_decomposition
    {S P : EventFlow} :
    PackageCandidate S P ->
      exists before after : EventFlow,
        S = List.append before (List.append P after) := by
  intro h
  exact h

end BEDC.GroundCompiler.PackageNameCertPrototype
