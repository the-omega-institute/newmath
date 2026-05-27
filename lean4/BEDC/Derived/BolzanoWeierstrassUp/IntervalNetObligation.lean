import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_interval_net_obligation [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalWindow retainedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalWindow ->
        Cont intervalWindow K retainedWindow ->
          PkgSig bundle retainedWindow pkg ->
            UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory intervalWindow ∧
              UnaryHistory retainedWindow ∧ Cont S K intervalWindow ∧
                Cont intervalWindow K retainedWindow ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle retainedWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier intervalRoute retainedRoute retainedPkg
  obtain ⟨SUnary, KUnary, _RUnary, _QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalWindow :=
    unary_cont_closed SUnary KUnary intervalRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed intervalUnary KUnary retainedRoute
  exact
    ⟨SUnary, KUnary, intervalUnary, retainedUnary, intervalRoute, retainedRoute,
      carrierPkg, retainedPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
