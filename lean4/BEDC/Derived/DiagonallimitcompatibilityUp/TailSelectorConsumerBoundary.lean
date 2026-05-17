import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityTailSelectorConsumerBoundary [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector consumed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector sealRow consumed →
          PkgSig bundle consumed pkg →
            UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory sealRow ∧
              UnaryHistory selector ∧ UnaryHistory consumed ∧ Cont diagonal windows selector ∧
                Cont selector sealRow consumed ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumed pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier diagonalWindowsSelector selectorSealConsumed consumedPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have consumedUnary : UnaryHistory consumed :=
    unary_cont_closed selectorUnary sealRowUnary selectorSealConsumed
  exact
    ⟨diagonalUnary, windowsUnary, sealRowUnary, selectorUnary, consumedUnary,
      diagonalWindowsSelector, selectorSealConsumed, provenancePkg, consumedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
