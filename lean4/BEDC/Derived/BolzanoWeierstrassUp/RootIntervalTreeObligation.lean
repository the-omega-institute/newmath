import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_root_interval_tree_obligation [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree dyadicRead streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalTree ->
        Cont intervalTree Q dyadicRead ->
          Cont dyadicRead E streamRead ->
            PkgSig bundle streamRead pkg ->
              UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory intervalTree ∧
                UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧ Cont S K intervalTree ∧
                  Cont intervalTree Q dyadicRead ∧ Cont dyadicRead E streamRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle streamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier intervalRoute dyadicRoute streamRoute streamPkg
  obtain ⟨SUnary, KUnary, _RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed SUnary KUnary intervalRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed intervalUnary QUnary dyadicRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary EUnary streamRoute
  exact
    ⟨SUnary, KUnary, intervalUnary, dyadicUnary, streamUnary, intervalRoute,
      dyadicRoute, streamRoute, carrierPkg, streamPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
