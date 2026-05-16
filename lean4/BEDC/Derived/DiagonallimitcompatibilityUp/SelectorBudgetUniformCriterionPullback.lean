import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.UniformCauchyCriterionUp

theorem DiagonalLimitCompatibilityCarrier_selector_budget_uniform_criterion_pullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      index modulus uTrans uRoutes uProv uName terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UniformCauchyCriterionPacket index windows modulus dyadic readback realSeal uTrans uRoutes
        uProv uName bundle pkg →
        Cont dyadic windows readback →
          Cont readback realSeal terminal →
            PkgSig bundle terminal pkg →
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory terminal ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal terminal ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle uName pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier packet dyadicWindowsReadback readbackRealSealTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _carrierDyadicWindowsReadback,
    _readbackRealSealRoute, _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨_indexUnary, _windowsUnary', _modulusUnary, _dyadicUnary', _readbackUnary',
    _realSealUnary', _uTransUnary, _uRoutesUnary, _uProvUnary, _uNameUnary,
    _indexWindowsModulus, _modulusDyadicReadback, _readbackRealSealTrans,
    _uTransRoutesProv, uNamePkg⟩ := packet
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, realSealUnary, terminalUnary,
      dyadicWindowsReadback, readbackRealSealTerminal, provenancePkg, uNamePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
