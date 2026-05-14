import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic selector →
        Cont selector windows locked →
          Cont locked readback endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory windows ∧
                UnaryHistory selector ∧ UnaryHistory locked ∧ UnaryHistory endpoint ∧
                  Cont diagonal dyadic selector ∧ Cont selector windows locked ∧
                    Cont locked readback endpoint ∧ Cont route cert transport ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicSelector selectorWindowsLocked lockedReadbackEndpoint endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary readbackUnary lockedReadbackEndpoint
  exact
    ⟨diagonalUnary, dyadicUnary, windowsUnary, selectorUnary, lockedUnary, endpointUnary,
      diagonalDyadicSelector, selectorWindowsLocked, lockedReadbackEndpoint,
      routeCertTransport, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
