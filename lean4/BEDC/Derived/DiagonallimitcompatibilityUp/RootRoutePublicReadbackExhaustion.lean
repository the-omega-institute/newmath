import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_route_public_readback_exhaustion
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows readback ->
        Cont readback sealRow route ->
          Cont route realSeal terminal ->
            PkgSig bundle terminal pkg ->
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory sealRow ∧ UnaryHistory route ∧ UnaryHistory realSeal ∧
                  UnaryHistory terminal ∧ Cont dyadic windows readback ∧
                    Cont readback sealRow route ∧ Cont route realSeal terminal ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier dyadicWindowsReadback readbackSealRoute routeRealSealTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _carrierDyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed readbackUnary sealRowUnary readbackSealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed routeUnary realSealUnary routeRealSealTerminal
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, sealRowUnary, routeUnary, realSealUnary,
      terminalUnary, dyadicWindowsReadback, readbackSealRoute, routeRealSealTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
