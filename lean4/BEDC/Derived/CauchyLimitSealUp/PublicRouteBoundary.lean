import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_public_route_boundary [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      Cont endpoint sealRow publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory dyadic ∧
            UnaryHistory diagonal ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
              UnaryHistory publicRead ∧ Cont source schedule dyadic ∧
                Cont dyadic diagonal sealRow ∧ Cont endpoint sealRow publicRead ∧
                  hsame endpoint (append provenance localCert) ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier endpointSealPublic publicPkg
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary sealUnary endpointSealPublic
  exact
    ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, sealUnary,
      endpointUnary, publicUnary, sourceScheduleDyadic, dyadicDiagonalSeal,
      endpointSealPublic, sameEndpoint, endpointPkg, publicPkg⟩

end BEDC.Derived.CauchyLimitSealUp
