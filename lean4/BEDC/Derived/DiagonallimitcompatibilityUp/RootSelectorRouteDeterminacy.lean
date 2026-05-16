import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorRouteDeterminacy [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selector' locked locked' endpoint endpoint' publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
      Cont diagonal windows selector' ->
      hsame selector selector' ->
      Cont selector readback locked ->
      Cont selector' readback locked' ->
      Cont locked realSeal endpoint ->
      Cont locked' realSeal endpoint' ->
      Cont endpoint transport publicRead ->
      Cont endpoint' transport publicRead' ->
      PkgSig bundle publicRead pkg ->
      PkgSig bundle publicRead' pkg ->
        hsame locked locked' ∧ hsame endpoint endpoint' ∧ hsame publicRead publicRead' ∧
          UnaryHistory publicRead ∧ UnaryHistory publicRead' ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro carrier diagonalWindowsSelector diagonalWindowsSelector' sameSelector
    selectorReadbackLocked selectorReadbackLocked' lockedRealSealEndpoint
    lockedRealSealEndpoint' endpointTransportPublic endpointTransportPublic'
    _publicPkg _publicPkg'
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have selectorUnary' : UnaryHistory selector' :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector'
  have sameLocked : hsame locked locked' :=
    cont_respects_hsame sameSelector (hsame_refl readback) selectorReadbackLocked
      selectorReadbackLocked'
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have lockedUnary' : UnaryHistory locked' :=
    unary_cont_closed selectorUnary' readbackUnary selectorReadbackLocked'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLocked (hsame_refl realSeal) lockedRealSealEndpoint
      lockedRealSealEndpoint'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed lockedUnary' realSealUnary lockedRealSealEndpoint'
  have samePublicRead : hsame publicRead publicRead' :=
    cont_respects_hsame sameEndpoint (hsame_refl transport) endpointTransportPublic
      endpointTransportPublic'
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportPublic
  have publicReadUnary' : UnaryHistory publicRead' :=
    unary_cont_closed endpointUnary' transportUnary endpointTransportPublic'
  exact
    ⟨sameLocked, sameEndpoint, samePublicRead, publicReadUnary, publicReadUnary',
      provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
