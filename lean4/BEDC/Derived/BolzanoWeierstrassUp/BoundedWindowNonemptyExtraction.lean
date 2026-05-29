import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_bounded_window_nonempty_extraction
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedCell sourceWindow nextIndex readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K retainedCell ->
        Cont retainedCell S sourceWindow ->
          Cont sourceWindow R nextIndex ->
            Cont nextIndex Q readback ->
              PkgSig bundle readback pkg ->
                UnaryHistory retainedCell ∧ UnaryHistory sourceWindow ∧
                  UnaryHistory nextIndex ∧ UnaryHistory readback ∧
                    Cont S K retainedCell ∧ Cont retainedCell S sourceWindow ∧
                      Cont sourceWindow R nextIndex ∧ Cont nextIndex Q readback ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier retainedRoute sourceWindowRoute nextIndexRoute readbackRoute readbackPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed SUnary KUnary retainedRoute
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed retainedUnary SUnary sourceWindowRoute
  have nextIndexUnary : UnaryHistory nextIndex :=
    unary_cont_closed sourceWindowUnary RUnary nextIndexRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed nextIndexUnary QUnary readbackRoute
  exact
    ⟨retainedUnary, sourceWindowUnary, nextIndexUnary, readbackUnary, retainedRoute,
      sourceWindowRoute, nextIndexRoute, readbackRoute, carrierPkg, readbackPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
