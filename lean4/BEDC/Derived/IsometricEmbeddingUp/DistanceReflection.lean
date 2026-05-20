import BEDC.Derived.IsometricEmbeddingUp

namespace BEDC.Derived.IsometricEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IsometricEmbeddingCarrier_distance_reflection [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧ UnaryHistory reflection ∧
        Cont sourceDistance targetDistance reflection ∧ PkgSig bundle reflection pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, sourceDistanceUnary, targetDistanceUnary,
    reflectionUnary, _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
      _sourceGraph, distanceReflection, reflectionPkg, _localSemantic⟩ := carrier
  exact
    ⟨sourceDistanceUnary, targetDistanceUnary, reflectionUnary, distanceReflection,
      reflectionPkg⟩

end BEDC.Derived.IsometricEmbeddingUp
