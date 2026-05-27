import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_interval_net_choice_free_retention [AskSetup]
    [PackageSetup]
    {S K R Q E H C P N retainedSchedule retainedReadback clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedSchedule ->
        Cont retainedSchedule Q retainedReadback ->
          Cont retainedReadback E clusterSeal ->
            PkgSig bundle clusterSeal pkg ->
              UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory retainedSchedule ∧
                UnaryHistory retainedReadback ∧ UnaryHistory clusterSeal ∧
                  Cont K R retainedSchedule ∧ Cont retainedSchedule Q retainedReadback ∧
                    Cont retainedReadback E clusterSeal ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle clusterSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier retainedRoute readbackRoute clusterRoute clusterPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedSchedule :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory retainedReadback :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  exact
    ⟨KUnary, RUnary, retainedUnary, readbackUnary, clusterUnary, retainedRoute,
      readbackRoute, clusterRoute, carrierPkg, clusterPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
