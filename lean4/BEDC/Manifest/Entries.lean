import BEDC.Manifest.Core
import BEDC.BaseReflection
import BEDC.FKernel.Gap
import BEDC.GroundCompiler
import BEDC.Derived.HolonomyUp
import BEDC.Derived.KKTUp
import BEDC.Derived.SpectralMeasureUp
import BEDC.Reflection
import BEDC.Capstone.EmptyFableMachine

namespace BEDC.Manifest

def manifest : List ClaimEntry := [
  ⟨"sec:base-reflection-lean-scaffold-contract",
    "BEDC.BaseReflection.PackageReflection_base",
    _, @BEDC.BaseReflection.PackageReflection_base⟩,
  ⟨"TBD",
    "BEDC.BaseReflection.PackageReflection_base_witness_chain",
    _, @BEDC.BaseReflection.PackageReflection_base_witness_chain⟩,
  ⟨"TBD",
    "BEDC.BaseReflection.PackageReflection_base_three_step_chain",
    _, @BEDC.BaseReflection.PackageReflection_base_three_step_chain⟩,
  ⟨"TBD",
    "BEDC.BaseReflection.TokUnique_replacement",
    _, @BEDC.BaseReflection.TokUnique_replacement⟩,
  ⟨"TBD",
    "BEDC.BaseReflection.PsameBase_iff_constructor_witnesses",
    _, @BEDC.BaseReflection.PsameBase_iff_constructor_witnesses⟩,
  ⟨"TBD",
    "BEDC.BaseReflection.GeneratedSameSig_iff_witnesses",
    _, @BEDC.BaseReflection.GeneratedSameSig_iff_witnesses⟩,
  ⟨"sec:base-reflection-lean-scaffold-contract",
    "BEDC.BaseReflection.no_scaffold_laundering_coverage_soundness",
    _, @BEDC.BaseReflection.no_scaffold_laundering_coverage_soundness⟩,

  ⟨"TBD",
    "BEDC.GroundCompiler.MainTheorems.channel_bijection",
    _, @BEDC.GroundCompiler.MainTheorems.channel_bijection⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.MainTheorems.channel_code_lossless",
    _, @BEDC.GroundCompiler.MainTheorems.channel_code_lossless⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.MainTheorems.code_not_proof",
    _, @BEDC.GroundCompiler.MainTheorems.code_not_proof⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.MainTheorems.global_conservativity",
    _, @BEDC.GroundCompiler.MainTheorems.global_conservativity⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.SelfHostingCompilerFlow.no_self_compilation_without_ledger",
    _, @BEDC.GroundCompiler.SelfHostingCompilerFlow.no_self_compilation_without_ledger⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.SelfHostingCompilerFlow.self_compilation_preserves_provenance",
    _, @BEDC.GroundCompiler.SelfHostingCompilerFlow.self_compilation_preserves_provenance⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.DerivCertReports.p6_adequacy",
    _, @BEDC.GroundCompiler.DerivCertReports.p6_adequacy⟩,
  ⟨"TBD",
    "BEDC.GroundCompiler.TheoremProofPrototype.p7_adequacy",
    _, @BEDC.GroundCompiler.TheoremProofPrototype.p7_adequacy⟩,

  ⟨"TBD",
    "BEDC.Derived.HolonomyUp.HolonomyTransportPacket_namecert_obligation_surface",
    _, @BEDC.Derived.HolonomyUp.HolonomyTransportPacket_namecert_obligation_surface⟩,
  ⟨"TBD",
    "BEDC.Derived.KKTUp.KKTPrimalDualPacket_namecert_obligation_surface",
    _, @BEDC.Derived.KKTUp.KKTPrimalDualPacket_namecert_obligation_surface⟩,
  ⟨"TBD",
    "BEDC.Derived.SpectralMeasureUp.SpectralMeasureFinitePacket_namecert_obligation_surface",
    _, @BEDC.Derived.SpectralMeasureUp.SpectralMeasureFinitePacket_namecert_obligation_surface⟩,

  ⟨"TBD",
    "BEDC.FKernel.Gap.domain_transport",
    _, @BEDC.FKernel.Gap.domain_transport⟩,
  ⟨"TBD",
    "BEDC.FKernel.Gap.DomainPolicy_iff_transport",
    _, @BEDC.FKernel.Gap.DomainPolicy_iff_transport⟩,
  ⟨"TBD",
    "BEDC.FKernel.Gap.DomainPolicy_iff_transport_and_invariance",
    _, @BEDC.FKernel.Gap.DomainPolicy_iff_transport_and_invariance⟩,
  ⟨"TBD",
    "BEDC.FKernel.Gap.inGapSig_transport_iff_with_signature_witnesses",
    _, @BEDC.FKernel.Gap.inGapSig_transport_iff_with_signature_witnesses⟩,
  ⟨"sec:proof-sprint-globalization-classifies-by-signatures",
    "BEDC.FKernel.Gap.proof_sprint_globalization_classifies_by_signatures",
    _, @BEDC.FKernel.Gap.proof_sprint_globalization_classifies_by_signatures⟩,
  ⟨"sec:proof-spine-composite-gap-coverage",
    "BEDC.FKernel.Gap.proof_spine_composite_gap_coverage",
    _, @BEDC.FKernel.Gap.proof_spine_composite_gap_coverage⟩,
  ⟨"sec:ledger-composition-principle-proof-standing",
    "BEDC.FKernel.Gap.ledger_composition_principle_proof_standing",
    _, @BEDC.FKernel.Gap.ledger_composition_principle_proof_standing⟩,

  ⟨"sec:empty-fable-machine-traces",
    "BEDC.Capstone.EmptyFableMachine.trace_hsame_transport",
    _, @BEDC.Capstone.EmptyFableMachine.trace_hsame_transport⟩,
  ⟨"sec:empty-fable-machine-ledger",
    "BEDC.Capstone.EmptyFableMachine.fable_ledger_sound",
    _, @BEDC.Capstone.EmptyFableMachine.fable_ledger_sound⟩,
  ⟨"sec:type-checking-as-classifier-membership",
    "BEDC.Reflection.type_checking_as_ext_membership_proof",
    _, @BEDC.Reflection.type_checking_as_ext_membership_proof⟩,
  ⟨"sec:compilation-as-namecert-morphism",
    "BEDC.Reflection.compilation_as_namecert_morphism_proof",
    _, @BEDC.Reflection.compilation_as_namecert_morphism_proof⟩
]

/-- Wellformedness 的可观察推论: manifest 里每条 claim 都至少有一个证明 witness。
    实质内容由 Lean 在 elaborate `manifest` 时做的 type-check 承载 (依赖字段 proof : prop)。 -/
theorem manifest_wellformed : ∀ e ∈ manifest, Nonempty e.prop :=
  fun e _ => ⟨e.proof⟩

end BEDC.Manifest
