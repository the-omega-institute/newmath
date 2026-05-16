import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitSelectorBudgetRealLimitUniquenessPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked uniquenessRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selector ->
        Cont selector windows locked ->
          Cont locked readback uniquenessRead ->
            Cont uniquenessRead realSeal completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory selector ∧ UnaryHistory locked ∧ UnaryHistory uniquenessRead ∧
                  UnaryHistory completionRead ∧ Cont diagonal dyadic selector ∧
                    Cont selector windows locked ∧ Cont locked readback uniquenessRead ∧
                      Cont uniquenessRead realSeal completionRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicSelector selectorWindowsLocked lockedReadbackUniquenessRead
    uniquenessReadRealSealCompletionRead completionReadPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsLocked
  have uniquenessReadUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed lockedUnary readbackUnary lockedReadbackUniquenessRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed uniquenessReadUnary realSealUnary uniquenessReadRealSealCompletionRead
  exact
    ⟨selectorUnary, lockedUnary, uniquenessReadUnary, completionReadUnary,
      diagonalDyadicSelector, selectorWindowsLocked, lockedReadbackUniquenessRead,
      uniquenessReadRealSealCompletionRead, provenancePkg, completionReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
