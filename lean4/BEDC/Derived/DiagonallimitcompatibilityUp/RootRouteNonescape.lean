import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteNonescape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows rootRead →
        Cont readback realSeal endpoint →
          PkgSig bundle rootRead pkg →
            PkgSig bundle endpoint pkg →
              UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory rootRead ∧ UnaryHistory endpoint ∧
                  Cont diagonal windows rootRead ∧ Cont readback realSeal endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro carrier diagonalWindowsRoot readbackRealSealEndpoint rootReadPkg endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsRoot
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, realSealUnary, rootReadUnary,
      endpointUnary, diagonalWindowsRoot, readbackRealSealEndpoint, provenancePkg,
      rootReadPkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
