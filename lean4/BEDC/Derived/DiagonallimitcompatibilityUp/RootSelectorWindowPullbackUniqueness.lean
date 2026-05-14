import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorWindowPullbackUniqueness
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selector' locked locked' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
      Cont diagonal windows selector' →
      hsame selector selector' →
      Cont selector readback locked →
      Cont selector' readback locked' →
      Cont locked realSeal endpoint →
      Cont locked' realSeal endpoint' →
      PkgSig bundle endpoint pkg →
      PkgSig bundle endpoint' pkg →
        hsame locked locked' ∧ hsame endpoint endpoint' ∧ UnaryHistory locked ∧
          UnaryHistory locked' ∧ UnaryHistory endpoint ∧ UnaryHistory endpoint' ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier diagonalWindowsSelector diagonalWindowsSelector' sameSelector
    selectorReadbackLocked selectorReadbackLocked' lockedRealSealEndpoint
    lockedRealSealEndpoint' _endpointPkg _endpointPkg'
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have lockedSame : hsame locked locked' :=
    cont_respects_hsame sameSelector (hsame_refl readback) selectorReadbackLocked
      selectorReadbackLocked'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame lockedSame (hsame_refl realSeal) lockedRealSealEndpoint
      lockedRealSealEndpoint'
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have selectorUnary' : UnaryHistory selector' :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector'
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have lockedUnary' : UnaryHistory locked' :=
    unary_cont_closed selectorUnary' readbackUnary selectorReadbackLocked'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed lockedUnary' realSealUnary lockedRealSealEndpoint'
  exact
    ⟨lockedSame, endpointSame, lockedUnary, lockedUnary', endpointUnary, endpointUnary',
      provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
