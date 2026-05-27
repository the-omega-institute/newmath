import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_subsequence_nonescape [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedCell selectedWindow readbackWindow clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedCell ->
        Cont retainedCell R selectedWindow ->
          Cont selectedWindow Q readbackWindow ->
            Cont readbackWindow E clusterSeal ->
              PkgSig bundle clusterSeal pkg ->
                UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                  UnaryHistory retainedCell ∧ UnaryHistory selectedWindow ∧
                    UnaryHistory readbackWindow ∧ UnaryHistory clusterSeal ∧
                      Cont K R retainedCell ∧ Cont retainedCell R selectedWindow ∧
                        Cont selectedWindow Q readbackWindow ∧
                          Cont readbackWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle clusterSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier retainedRoute selectedRoute readbackRoute clusterRoute clusterPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed KUnary RUnary retainedRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed retainedUnary RUnary selectedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed selectedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  exact
    ⟨KUnary, RUnary, QUnary, EUnary, retainedUnary, selectedUnary, readbackUnary,
      clusterUnary, retainedRoute, selectedRoute, readbackRoute, clusterRoute,
      carrierPkg, clusterPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
