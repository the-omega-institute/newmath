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

theorem DiagonalLimitCompatibilityCarrier_selector_budget_uniform_real_exit
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      uIndex uWindows uModulus uTolerance uTail uSeal uTransports uRoutes uProvenance uName
      exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UniformCauchyCriterionPacket uIndex uWindows uModulus uTolerance uTail uSeal
        uTransports uRoutes uProvenance uName bundle pkg →
        hsame uWindows windows →
          hsame uTolerance dyadic →
            hsame uTail readback →
              hsame uSeal realSeal →
                Cont uTail uSeal exitRead →
                  PkgSig bundle exitRead pkg →
                    UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
                      UnaryHistory realSeal ∧ UnaryHistory uIndex ∧ UnaryHistory exitRead ∧
                        hsame uWindows windows ∧ hsame uTolerance dyadic ∧
                          hsame uTail readback ∧ hsame uSeal realSeal ∧
                            Cont uTail uSeal exitRead ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle uName pkg ∧ PkgSig bundle exitRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro carrier packet sameWindows sameTolerance sameTail sameSeal tailSealExit exitPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨uIndexUnary, _uWindowsUnary, _uModulusUnary, _uToleranceUnary, uTailUnary,
    uSealUnary, _uTransportsUnary, _uRoutesUnary, _uProvenanceUnary, _uNameUnary,
    _uIndexWindowsModulus, _uModulusToleranceTail, _uTailSealTransports,
    _uTransportsRoutesProvenance, uNamePkg⟩ := packet
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed uTailUnary uSealUnary tailSealExit
  exact
    ⟨windowsUnary, dyadicUnary, readbackUnary, realSealUnary, uIndexUnary, exitUnary,
      sameWindows, sameTolerance, sameTail, sameSeal, tailSealExit, provenancePkg,
      uNamePkg, exitPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
