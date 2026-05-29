import BEDC.Derived.BolzanoWeierstrassUp.FiniteIntervalTreeInduction
import BEDC.Derived.BolzanoWeierstrassUp.RetainedCellMonotonicity

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_bounded_window_induction [AskSetup] [PackageSetup]
    {S K R Q E H C P N rootCell retainedCell boundedWindow nextLedger readback
      refinedCell refinedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K rootCell ->
        Cont rootCell K retainedCell ->
          Cont retainedCell S boundedWindow ->
            Cont boundedWindow R nextLedger ->
              Cont nextLedger Q readback ->
                Cont retainedCell K refinedCell ->
                  Cont refinedCell S refinedWindow ->
                    PkgSig bundle readback pkg ->
                      UnaryHistory rootCell ∧ UnaryHistory retainedCell ∧
                        UnaryHistory boundedWindow ∧ UnaryHistory nextLedger ∧
                          UnaryHistory readback ∧ UnaryHistory refinedCell ∧
                            UnaryHistory refinedWindow ∧ Cont S K rootCell ∧
                              Cont rootCell K retainedCell ∧
                                Cont retainedCell S boundedWindow ∧
                                  Cont boundedWindow R nextLedger ∧
                                    Cont nextLedger Q readback ∧
                                      Cont retainedCell K refinedCell ∧
                                        Cont refinedCell S refinedWindow ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier rootRoute retainedRoute boundedRoute ledgerRoute readbackRoute
    refinedRoute refinedWindowRoute readbackPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have rootUnary : UnaryHistory rootCell :=
    unary_cont_closed SUnary KUnary rootRoute
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed rootUnary KUnary retainedRoute
  have boundedUnary : UnaryHistory boundedWindow :=
    unary_cont_closed retainedUnary SUnary boundedRoute
  have ledgerUnary : UnaryHistory nextLedger :=
    unary_cont_closed boundedUnary RUnary ledgerRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed ledgerUnary QUnary readbackRoute
  have refinedUnary : UnaryHistory refinedCell :=
    unary_cont_closed retainedUnary KUnary refinedRoute
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_cont_closed refinedUnary SUnary refinedWindowRoute
  exact
    ⟨rootUnary, retainedUnary, boundedUnary, ledgerUnary, readbackUnary,
      refinedUnary, refinedWindowUnary, rootRoute, retainedRoute, boundedRoute,
      ledgerRoute, readbackRoute, refinedRoute, refinedWindowRoute, carrierPkg,
      readbackPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
