import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityStreamNameBudgetTriad [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal2 triangle2 sealRow2 dyadic2 windows2 readback2 realSeal2 transport2 route2
      provenance2 cert2 terminal terminal2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      DiagonalLimitCompatibilityCarrier diagonal2 triangle2 sealRow2 dyadic2 windows2 readback2
          realSeal2 transport2 route2 provenance2 cert2 bundle pkg ->
        hsame dyadic dyadic2 ->
          hsame windows windows2 ->
            hsame readback readback2 ->
              hsame realSeal realSeal2 ->
                Cont readback realSeal terminal ->
                  Cont readback2 realSeal2 terminal2 ->
                    PkgSig bundle terminal pkg ->
                      PkgSig bundle terminal2 pkg ->
                        hsame terminal terminal2 ∧ UnaryHistory windows ∧
                          UnaryHistory readback ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle provenance2 pkg ∧ PkgSig bundle terminal pkg ∧
                              PkgSig bundle terminal2 pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro carrier carrier2 _sameDyadic _sameWindows sameReadback sameRealSeal readbackTerminal
    readbackTerminal2 terminalPkg terminal2Pkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨_diagonalUnary2, _triangleUnary2, _sealRowUnary2, _dyadicUnary2, _windowsUnary2,
    _readbackUnary2, _realSealUnary2, _transportUnary2, _routeUnary2, _provenanceUnary2,
    _certUnary2, _diagonalTriangleSeal2, _dyadicWindowsReadback2, _readbackRealSealRoute2,
    _routeCertTransport2, provenance2Pkg⟩ := carrier2
  have sameTerminal : hsame terminal terminal2 :=
    cont_respects_hsame sameReadback sameRealSeal readbackTerminal readbackTerminal2
  exact
    ⟨sameTerminal, windowsUnary, readbackUnary, provenancePkg, provenance2Pkg,
      terminalPkg, terminal2Pkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
