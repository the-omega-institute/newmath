import BEDC.Derived.LipschitzMapUp

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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
