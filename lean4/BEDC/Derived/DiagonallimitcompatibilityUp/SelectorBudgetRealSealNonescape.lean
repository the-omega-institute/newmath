import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_real_seal_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector sealEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector realSeal sealEndpoint →
          PkgSig bundle sealEndpoint pkg →
            UnaryHistory selector ∧ UnaryHistory realSeal ∧ UnaryHistory sealEndpoint ∧
              Cont diagonal windows selector ∧ Cont selector realSeal sealEndpoint ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle sealEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalWindowsSelector selectorRealSealEndpoint endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have endpointUnary : UnaryHistory sealEndpoint :=
    unary_cont_closed selectorUnary realSealUnary selectorRealSealEndpoint
  exact
    ⟨selectorUnary, realSealUnary, endpointUnary, diagonalWindowsSelector,
      selectorRealSealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
