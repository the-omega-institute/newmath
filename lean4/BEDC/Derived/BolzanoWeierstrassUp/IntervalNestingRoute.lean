import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_interval_nesting_route [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalRead retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalRead ->
        Cont intervalRead R retainedRead ->
          UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory intervalRead ∧
            UnaryHistory retainedRead ∧ Cont S K intervalRead ∧
              Cont intervalRead R retainedRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier intervalRoute retainedRoute
  obtain ⟨SUnary, KUnary, RUnary, _QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed SUnary KUnary intervalRoute
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed intervalUnary RUnary retainedRoute
  exact
    ⟨SUnary, KUnary, RUnary, intervalUnary, retainedUnary, intervalRoute,
      retainedRoute, carrierPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
