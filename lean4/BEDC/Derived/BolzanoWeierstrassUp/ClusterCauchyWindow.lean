import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cluster_cauchy_window
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedCell laterCell selectedWindow readbackWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
    (retainedRoute : Cont K R retainedCell)
    (tailRoute : Cont retainedCell H laterCell)
    (windowRoute : Cont laterCell R selectedWindow)
    (readbackRoute : Cont selectedWindow Q readbackWindow)
    (readbackPkg : PkgSig bundle readbackWindow pkg) :
    UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory retainedCell ∧
      UnaryHistory laterCell ∧ UnaryHistory selectedWindow ∧ UnaryHistory readbackWindow ∧
        Cont K R retainedCell ∧ Cont retainedCell H laterCell ∧
          Cont laterCell R selectedWindow ∧ Cont selectedWindow Q readbackWindow ∧
            PkgSig bundle P pkg ∧ PkgSig bundle readbackWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, _EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed KUnary RUnary retainedRoute
  have laterUnary : UnaryHistory laterCell :=
    unary_cont_closed retainedUnary HUnary tailRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed laterUnary RUnary windowRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed selectedUnary QUnary readbackRoute
  exact
    ⟨KUnary, RUnary, QUnary, retainedUnary, laterUnary, selectedUnary, readbackUnary,
      retainedRoute, tailRoute, windowRoute, readbackRoute, carrierPkg, readbackPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
