import BEDC.Derived.MetricClosedBallUp

namespace BEDC.Derived.MetricClosedBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricClosedBallCarrier_center_transport_scope [AskSetup] [PackageSetup]
    {X d c r rho m H C P N X' d' c' r' rho' m' H' C' P' N' centerRead centerRead'
      boundary boundary' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ->
      MetricClosedBallCarrier X' d' c' r' rho' m' H' C' P' N' bundle pkg ->
        hsame X X' ->
          hsame c c' ->
            Cont X c centerRead ->
              Cont X' c' centerRead' ->
                Cont centerRead rho boundary ->
                  Cont centerRead' rho' boundary' ->
                    hsame centerRead centerRead' ∧ UnaryHistory centerRead ∧
                      UnaryHistory centerRead' ∧ UnaryHistory boundary ∧
                        UnaryHistory boundary' ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' sameMetricSpace sameCenter centerRoute transportedCenterRoute
    boundaryRoute transportedBoundaryRoute
  obtain ⟨xUnary, _dUnary, cUnary, _rUnary, rhoUnary, _mUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceRoute, _membershipRoute, _nameRoute, _membershipSame,
    provenancePkg⟩ := carrier
  obtain ⟨xUnary', _dUnary', cUnary', _rUnary', rhoUnary', _mUnary', _HUnary',
    _CUnary', _PUnary', _NUnary', _sourceRoute', _membershipRoute', _nameRoute',
    _membershipSame', _pkgSig'⟩ := carrier'
  have centerStable : hsame centerRead centerRead' :=
    cont_respects_hsame sameMetricSpace sameCenter centerRoute transportedCenterRoute
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed xUnary cUnary centerRoute
  have transportedCenterUnary : UnaryHistory centerRead' :=
    unary_cont_closed xUnary' cUnary' transportedCenterRoute
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed centerUnary rhoUnary boundaryRoute
  have transportedBoundaryUnary : UnaryHistory boundary' :=
    unary_cont_closed transportedCenterUnary rhoUnary' transportedBoundaryRoute
  exact
    ⟨centerStable, centerUnary, transportedCenterUnary, boundaryUnary,
      transportedBoundaryUnary, provenancePkg⟩

end BEDC.Derived.MetricClosedBallUp
