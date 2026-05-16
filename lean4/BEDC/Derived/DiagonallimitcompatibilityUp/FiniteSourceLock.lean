import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityFiniteSourceLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal route ->
        Cont route cert completion ->
          PkgSig bundle completion pkg ->
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory route ∧ UnaryHistory cert ∧
                  UnaryHistory completion ∧ Cont diagonal triangle sealRow ∧
                    Cont dyadic windows readback ∧ Cont readback realSeal route ∧
                      Cont route cert completion ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier readbackRealSealRoute routeCertCompletion completionPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, _carrierReadbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed routeUnary certUnary routeCertCompletion
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, routeUnary, certUnary, completionUnary, diagonalTriangleSeal,
      dyadicWindowsReadback, readbackRealSealRoute, routeCertCompletion, provenancePkg,
      completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
