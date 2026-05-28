import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_real_cluster_seal [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow readbackWindow clusterSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedWindow ->
        Cont retainedWindow Q readbackWindow ->
          Cont readbackWindow E clusterSeal ->
            Cont clusterSeal H realSeal ->
              PkgSig bundle realSeal pkg ->
                UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                  UnaryHistory E ∧ UnaryHistory retainedWindow ∧
                    UnaryHistory readbackWindow ∧ UnaryHistory clusterSeal ∧
                      UnaryHistory realSeal ∧ Cont K R retainedWindow ∧
                        Cont retainedWindow Q readbackWindow ∧
                          Cont readbackWindow E clusterSeal ∧
                            Cont clusterSeal H realSeal ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier retainedRoute readbackRoute clusterRoute realSealRoute realSealPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed clusterUnary HUnary realSealRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, retainedUnary, readbackUnary,
      clusterUnary, realSealUnary, retainedRoute, readbackRoute, clusterRoute,
      realSealRoute, carrierPkg, realSealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
