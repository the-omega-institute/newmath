import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealUp_StdBridge [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont endpoint sealRow bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          UnaryHistory bridgeRead ∧ hsame endpoint (append provenance localCert) ∧
            Cont endpoint sealRow bridgeRead ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier endpointSealBridge bridgePkg
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary sealUnary endpointSealBridge
  exact ⟨bridgeUnary, sameEndpoint, endpointSealBridge, endpointPkg, bridgePkg⟩

end BEDC.Derived.CauchyLimitSealUp
