import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_consumer_nonescape [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootRead windowRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic rootRead ->
        Cont rootRead windows windowRead ->
          Cont windowRead cert finalRead ->
            PkgSig bundle finalRead pkg ->
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory cert ∧ UnaryHistory rootRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory finalRead ∧ Cont diagonal dyadic rootRead ∧
                    Cont rootRead windows windowRead ∧ Cont windowRead cert finalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier diagonalDyadicRoot rootWindowsWindow windowCertFinal finalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rootUnary windowsUnary rootWindowsWindow
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed windowUnary certUnary windowCertFinal
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, certUnary, rootUnary, windowUnary,
      finalUnary, diagonalDyadicRoot, rootWindowsWindow, windowCertFinal, provenancePkg,
      finalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
