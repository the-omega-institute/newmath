import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_budget_real_completion_factorization
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorRead syncRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic selectorRead →
        Cont selectorRead windows syncRead →
          Cont syncRead realSeal completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory realSeal ∧ UnaryHistory selectorRead ∧ UnaryHistory syncRead ∧
                  UnaryHistory completionRead ∧ Cont diagonal dyadic selectorRead ∧
                    Cont selectorRead windows syncRead ∧
                      Cont syncRead realSeal completionRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicSelector selectorWindowsSync syncRealSealCompletion
    completionPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have syncUnary : UnaryHistory syncRead :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsSync
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed syncUnary realSealUnary syncRealSealCompletion
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, realSealUnary, selectorUnary, syncUnary,
      completionUnary, diagonalDyadicSelector, selectorWindowsSync, syncRealSealCompletion,
      provenancePkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
