import BEDC.GroundCompiler.MainTheorems

namespace BEDC.GroundCompiler.Audit

/-! ## Re-exports of GroundCompiler audit theorems

This module re-exports the BEDC.GroundCompiler audit-relevant theorems
in a single namespace for downstream consumers. Parallel to BEDC.MetaCIC.Audit. -/

-- Main statements
export BEDC.GroundCompiler.MainTheorems (
  GlobalConservativityStatement
  CompilerLayerAddressAnalysisStatement
  NoHiddenInputStreamingCompilerStatement
)

-- Main theorem witnesses
export BEDC.GroundCompiler.MainTheorems (
  global_conservativity
  compiler_layer_address_analysis_layer
  no_hidden_input_streaming_compiler
)

-- Compiler input and channel audit surface
export BEDC.GroundCompiler.MainTheorems (
  NoHiddenInputCompilerState
  no_hidden_input
  channel_bijection
  channel_code_lossless
  source_channel_separation
  carry_not_channel_rewrite
)

-- Generated structure and export boundaries
export BEDC.GroundCompiler.MainTheorems (
  GeneratedStructure
  SelfHostedCompiler
  AcceptedExport
  structure_emergence
  yaml_ast_output_only
  recognizer_generatedness
  self_hosting_removes_hidden_compiler
  accepted_export
  code_existence_not_export
  motif_existence_not_export
)

-- Canonical code and classifier witnesses
export BEDC.GroundCompiler.MainTheorems (
  CanonicalTheoremFlow
  LegalCanonicalTheoremCode
  theorem_code_bijection
  theorem_code_not_proof
  CanonicalChapterFlow
  LegalCanonicalChapterCode
  chapter_code_bijection
  classifier_quotient_many_to_one
  metric_conservativity
)

-- Cannot-claim registry
export BEDC.GroundCompiler.MainTheorems (
  CannotClaimKind
  CompilerCannotClaimEntry
  CannotClaimRegistryAdequate
  cannot_claim_registry_mandatory
)

end BEDC.GroundCompiler.Audit
