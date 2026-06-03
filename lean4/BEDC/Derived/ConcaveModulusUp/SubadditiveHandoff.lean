import BEDC.Derived.ConcaveModulusUp.NameCertObligations

namespace BEDC.Derived.ConcaveModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ConcaveModulusCarrier_subadditive_handoff [AskSetup] [PackageSetup]
    {modulus left right midpoint bound transport route provenance localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConcaveModulusCarrier modulus left right midpoint bound transport route provenance localName
        endpoint bundle pkg →
      Cont left right midpoint ∧ Cont midpoint bound endpoint ∧
        Cont transport route provenance ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro carrier
  obtain ⟨_modulusUnary, _leftUnary, _rightUnary, _midpointUnary, _boundUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary, _endpointUnary,
    leftRightMidpoint, midpointBoundEndpoint, transportRouteProvenance, _provenancePkg,
    endpointPkg⟩ := carrier
  exact ⟨leftRightMidpoint, midpointBoundEndpoint, transportRouteProvenance, endpointPkg⟩

end BEDC.Derived.ConcaveModulusUp
