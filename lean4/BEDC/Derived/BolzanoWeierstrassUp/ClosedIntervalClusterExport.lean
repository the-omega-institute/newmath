import BEDC.Derived.BolzanoWeierstrassUp.ClosedIntervalClusterHandoff

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_closed_interval_cluster_export [AskSetup] [PackageSetup]
    {S K R Q E H C P N boundedSource retainedCell subseqRead regularRead clusterSeal
      transportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K boundedSource ->
        Cont boundedSource K retainedCell ->
          Cont retainedCell R subseqRead ->
            Cont subseqRead Q regularRead ->
              Cont regularRead E clusterSeal ->
                Cont clusterSeal H transportRead ->
                  Cont transportRead C replayRead ->
                    PkgSig bundle replayRead pkg ->
                      UnaryHistory boundedSource ∧ UnaryHistory retainedCell ∧
                        UnaryHistory subseqRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory clusterSeal ∧ UnaryHistory transportRead ∧
                            UnaryHistory replayRead ∧ Cont S K boundedSource ∧
                              Cont boundedSource K retainedCell ∧
                                Cont retainedCell R subseqRead ∧
                                  Cont subseqRead Q regularRead ∧
                                    Cont regularRead E clusterSeal ∧
                                      Cont clusterSeal H transportRead ∧
                                        Cont transportRead C replayRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier boundedRoute retainedRoute subseqRoute regularRoute clusterRoute
    transportRoute replayRoute replayPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have boundedUnary : UnaryHistory boundedSource :=
    unary_cont_closed SUnary KUnary boundedRoute
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed boundedUnary KUnary retainedRoute
  have subseqUnary : UnaryHistory subseqRead :=
    unary_cont_closed retainedUnary RUnary subseqRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed subseqUnary QUnary regularRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed regularUnary EUnary clusterRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed clusterUnary HUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary CUnary replayRoute
  exact
    ⟨boundedUnary, retainedUnary, subseqUnary, regularUnary, clusterUnary,
      transportUnary, replayUnary, boundedRoute, retainedRoute, subseqRoute,
      regularRoute, clusterRoute, transportRoute, replayRoute, carrierPkg, replayPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
