import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityWindowFusion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      windowTriangle windowSeal windowReadback fused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows triangle windowTriangle ->
        Cont windows sealRow windowSeal ->
          Cont windows readback windowReadback ->
            Cont windowTriangle windowSeal fused ->
              PkgSig bundle fused pkg ->
                UnaryHistory windows ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
                  UnaryHistory readback ∧ UnaryHistory windowTriangle ∧
                    UnaryHistory windowSeal ∧ UnaryHistory windowReadback ∧
                      UnaryHistory fused ∧ Cont windows triangle windowTriangle ∧
                        Cont windows sealRow windowSeal ∧
                          Cont windows readback windowReadback ∧
                            Cont windowTriangle windowSeal fused ∧
                              Cont dyadic windows readback ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle fused pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier windowsTriangle windowSealRow windowsReadback windowTriangleSealFused fusedPkg
  obtain ⟨_diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have windowTriangleUnary : UnaryHistory windowTriangle :=
    unary_cont_closed windowsUnary triangleUnary windowsTriangle
  have windowSealUnary : UnaryHistory windowSeal :=
    unary_cont_closed windowsUnary sealUnary windowSealRow
  have windowReadbackUnary : UnaryHistory windowReadback :=
    unary_cont_closed windowsUnary readbackUnary windowsReadback
  have fusedUnary : UnaryHistory fused :=
    unary_cont_closed windowTriangleUnary windowSealUnary windowTriangleSealFused
  exact
    ⟨windowsUnary, triangleUnary, sealUnary, readbackUnary, windowTriangleUnary,
      windowSealUnary, windowReadbackUnary, fusedUnary, windowsTriangle, windowSealRow,
      windowsReadback, windowTriangleSealFused, dyadicWindowsReadback, provenancePkg,
      fusedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
