import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_cauchy_filter_basis_triad [AskSetup] [PackageSetup]
    {M R D W H C P N roundedRead filterRead netRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont M R roundedRead ->
        Cont roundedRead W filterRead ->
          Cont D W netRead ->
            Cont filterRead netRead handoffRead ->
              PkgSig bundle handoffRead pkg ->
                UnaryHistory roundedRead ∧ UnaryHistory filterRead ∧
                  UnaryHistory netRead ∧ UnaryHistory handoffRead ∧
                    Cont M R roundedRead ∧ Cont roundedRead W filterRead ∧
                      Cont D W netRead ∧ Cont filterRead netRead handoffRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: FormalBallCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier roundedRoute filterRoute netRoute handoffRoute handoffPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius,
    _dyadicWindowReplay, _transportReplay, provenancePkg⟩ := carrier
  have roundedReadUnary : UnaryHistory roundedRead :=
    unary_cont_closed metricUnary radiusUnary roundedRoute
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed roundedReadUnary windowUnary filterRoute
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed dyadicUnary windowUnary netRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed filterReadUnary netReadUnary handoffRoute
  exact
    ⟨roundedReadUnary, filterReadUnary, netReadUnary, handoffReadUnary, roundedRoute,
      filterRoute, netRoute, handoffRoute, provenancePkg, handoffPkg⟩

end BEDC.Derived.FormalBallUp
