import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySealSynchronizerBudgetHandoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorRead synchronizerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows selectorRead →
        Cont selectorRead realSeal synchronizerRead →
          PkgSig bundle synchronizerRead pkg →
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory selectorRead ∧
                UnaryHistory synchronizerRead ∧ Cont dyadic windows readback ∧
                  Cont dyadic windows selectorRead ∧
                    Cont selectorRead realSeal synchronizerRead ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle synchronizerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier dyadicWindowsSelector selectorRealSynchronizer synchronizerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsSelector
  have synchronizerReadUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed selectorReadUnary realSealUnary selectorRealSynchronizer
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, realSealUnary, selectorReadUnary,
      synchronizerReadUnary, dyadicWindowsReadback, dyadicWindowsSelector,
      selectorRealSynchronizer, provenancePkg, synchronizerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
