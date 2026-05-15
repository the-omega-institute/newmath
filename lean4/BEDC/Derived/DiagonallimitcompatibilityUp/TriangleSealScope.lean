import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTriangleSealScope [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triangleDyadic triangleWindow sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont triangle dyadic triangleDyadic ->
        Cont triangleDyadic windows triangleWindow ->
          Cont triangleWindow sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory triangle ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory sealRow ∧ UnaryHistory triangleDyadic ∧
                  UnaryHistory triangleWindow ∧ UnaryHistory sealRead ∧
                    Cont triangle dyadic triangleDyadic ∧
                      Cont triangleDyadic windows triangleWindow ∧
                        Cont triangleWindow sealRow sealRead ∧
                          Cont diagonal triangle sealRow ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro carrier triangleDyadicRoute triangleWindowRoute sealReadRoute sealReadPkg
  obtain ⟨_diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have triangleDyadicUnary : UnaryHistory triangleDyadic :=
    unary_cont_closed triangleUnary dyadicUnary triangleDyadicRoute
  have triangleWindowUnary : UnaryHistory triangleWindow :=
    unary_cont_closed triangleDyadicUnary windowsUnary triangleWindowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed triangleWindowUnary sealRowUnary sealReadRoute
  exact
    ⟨triangleUnary, dyadicUnary, windowsUnary, sealRowUnary, triangleDyadicUnary,
      triangleWindowUnary, sealReadUnary, triangleDyadicRoute, triangleWindowRoute,
      sealReadRoute, diagonalTriangleSeal, provenancePkg, sealReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
