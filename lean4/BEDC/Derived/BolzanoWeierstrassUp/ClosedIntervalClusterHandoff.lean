import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_closed_interval_cluster_handoff [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalWindow retainedWindow subseqWindow readbackWindow
      clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalWindow ->
        Cont intervalWindow K retainedWindow ->
          Cont retainedWindow R subseqWindow ->
            Cont subseqWindow Q readbackWindow ->
              Cont readbackWindow E clusterSeal ->
                PkgSig bundle clusterSeal pkg ->
                  UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                    UnaryHistory E ∧ UnaryHistory retainedWindow ∧
                      UnaryHistory subseqWindow ∧ UnaryHistory readbackWindow ∧
                        UnaryHistory clusterSeal ∧ Cont S K intervalWindow ∧
                          Cont intervalWindow K retainedWindow ∧
                            Cont retainedWindow R subseqWindow ∧
                              Cont subseqWindow Q readbackWindow ∧
                                Cont readbackWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle clusterSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier intervalRoute retainedRoute subseqRoute readbackRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalWindow :=
    unary_cont_closed SUnary KUnary intervalRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed intervalUnary KUnary retainedRoute
  have subseqUnary : UnaryHistory subseqWindow :=
    unary_cont_closed retainedUnary RUnary subseqRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed subseqUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, retainedUnary, subseqUnary,
      readbackUnary, clusterUnary, intervalRoute, retainedRoute, subseqRoute,
      readbackRoute, clusterRoute, carrierPkg, clusterPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
