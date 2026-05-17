import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCriterionUniformSealPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      criterion uniform sealPullback terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory criterion →
        UnaryHistory uniform →
          Cont criterion uniform sealPullback →
            Cont sealPullback realSeal terminal →
              PkgSig bundle terminal pkg →
                UnaryHistory criterion ∧ UnaryHistory uniform ∧ UnaryHistory sealPullback ∧
                  UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                    Cont criterion uniform sealPullback ∧
                      Cont sealPullback realSeal terminal ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalLimitCompatibilityCarrier
  intro carrier criterionUnary uniformUnary criterionUniformSealPullback
    sealPullbackRealSealTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealPullbackUnary : UnaryHistory sealPullback :=
    unary_cont_closed criterionUnary uniformUnary criterionUniformSealPullback
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealPullbackUnary realSealUnary sealPullbackRealSealTerminal
  exact
    ⟨criterionUnary, uniformUnary, sealPullbackUnary, realSealUnary, terminalUnary,
      criterionUniformSealPullback, sealPullbackRealSealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
