import BEDC.Derived.LipschitzMapUp

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LipschitzMapCarrier_common_bound_completion_route [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert realSeal
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont modulus routes realSeal ->
        Cont realSeal provenance completionRead ->
          PkgSig bundle realSeal pkg ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory bound ∧
                UnaryHistory graph ∧ UnaryHistory modulus ∧ UnaryHistory routes ∧
                  UnaryHistory provenance ∧ UnaryHistory realSeal ∧
                    UnaryHistory completionRead ∧ Cont graph bound modulus ∧
                      Cont modulus routes provenance ∧ Cont modulus routes realSeal ∧
                        Cont realSeal provenance completionRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle realSeal pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier modulusRoutesRealSeal realSealProvenanceCompletion realSealPkg completionPkg
  obtain ⟨sourceUnary, targetUnary, boundUnary, graphUnary, _transportsUnary, routesUnary,
    _localCertUnary, graphBoundModulus, modulusRoutesProvenance, provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesProvenance
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesRealSeal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceCompletion
  exact
    ⟨sourceUnary, targetUnary, boundUnary, graphUnary, modulusUnary, routesUnary,
      provenanceUnary, realSealUnary, completionUnary, graphBoundModulus,
      modulusRoutesProvenance, modulusRoutesRealSeal, realSealProvenanceCompletion,
      provenancePkg, realSealPkg, completionPkg⟩

theorem LipschitzMapCarrier_common_bound_completion_namecert_route [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert realSeal
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont modulus routes realSeal ->
        Cont realSeal provenance completionRead ->
          PkgSig bundle realSeal pkg ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row modulus ∨ hsame row realSeal ∨ hsame row completionRead)
                  (fun row : BHist =>
                    hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory completionRead ∧ Cont modulus routes realSeal ∧
                  Cont realSeal provenance completionRead ∧ PkgSig bundle completionRead pkg := by
  intro carrier modulusRoutesRealSeal realSealProvenanceCompletion realSealPkg completionPkg
  have common :=
    LipschitzMapCarrier_common_bound_completion_route carrier modulusRoutesRealSeal
      realSealProvenanceCompletion realSealPkg completionPkg
  obtain
    ⟨_sourceUnary, _targetUnary, _boundUnary, _graphUnary, _modulusUnary,
      _routesUnary, _provenanceUnary, _realSealUnary, completionUnary,
      _graphBoundModulus, _modulusRoutesProvenance, _modulusRoutesRealSeal,
      _realSealProvenanceCompletion, _provenancePkg, _realSealPkg,
      _completionPkg⟩ := common
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row modulus ∨ hsame row realSeal ∨ hsame row completionRead)
          (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionPkg⟩
  }
  exact
    ⟨cert, completionUnary, modulusRoutesRealSeal, realSealProvenanceCompletion,
      completionPkg⟩

theorem LipschitzMapCarrier_boundary_completion_consumer_route [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer realSeal
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont provenance localCert consumer ->
        Cont modulus routes realSeal ->
          Cont realSeal consumer completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory modulus ∧ UnaryHistory consumer ∧ UnaryHistory realSeal ∧
                UnaryHistory completionRead ∧ Cont graph bound modulus ∧
                  Cont modulus routes provenance ∧ Cont provenance localCert consumer ∧
                    Cont modulus routes realSeal ∧ Cont realSeal consumer completionRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier provenanceLocalCertConsumer modulusRoutesRealSeal realSealConsumerCompletion
    completionPkg
  have boundary :=
    LipschitzMapCarrier_uniform_modulus_boundary carrier provenanceLocalCertConsumer
  obtain
    ⟨modulusUnary, consumerUnary, graphBoundModulus, modulusRoutesProvenance,
      provenancePkg⟩ := boundary
  obtain ⟨_sourceUnary, _targetUnary, _boundUnary, _graphUnary, _transportsUnary,
    routesUnary, _localCertUnary, _graphBoundModulus, _modulusRoutesProvenance,
    _provenancePkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesRealSeal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realSealUnary consumerUnary realSealConsumerCompletion
  exact
    ⟨modulusUnary, consumerUnary, realSealUnary, completionUnary, graphBoundModulus,
      modulusRoutesProvenance, provenanceLocalCertConsumer, modulusRoutesRealSeal,
      realSealConsumerCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.LipschitzMapUp
