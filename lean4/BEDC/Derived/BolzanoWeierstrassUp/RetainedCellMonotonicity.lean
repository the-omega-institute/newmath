import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_retained_cell_monotonicity
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N earlierCell laterCell earlierWindow laterWindow
      nextLedger readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K earlierCell ->
        Cont earlierCell K laterCell ->
          Cont earlierCell S earlierWindow ->
            Cont laterCell S laterWindow ->
              Cont laterWindow R nextLedger ->
                Cont nextLedger Q readback ->
                  PkgSig bundle readback pkg ->
                    UnaryHistory earlierCell ∧ UnaryHistory laterCell ∧
                      UnaryHistory earlierWindow ∧ UnaryHistory laterWindow ∧
                        UnaryHistory nextLedger ∧ UnaryHistory readback ∧
                          Cont S K earlierCell ∧ Cont earlierCell K laterCell ∧
                            Cont earlierCell S earlierWindow ∧
                              Cont laterCell S laterWindow ∧
                                Cont laterWindow R nextLedger ∧
                                  Cont nextLedger Q readback ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier earlierRoute laterRoute earlierWindowRoute laterWindowRoute
    ledgerRoute readbackRoute readbackPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have earlierUnary : UnaryHistory earlierCell :=
    unary_cont_closed SUnary KUnary earlierRoute
  have laterUnary : UnaryHistory laterCell :=
    unary_cont_closed earlierUnary KUnary laterRoute
  have earlierWindowUnary : UnaryHistory earlierWindow :=
    unary_cont_closed earlierUnary SUnary earlierWindowRoute
  have laterWindowUnary : UnaryHistory laterWindow :=
    unary_cont_closed laterUnary SUnary laterWindowRoute
  have ledgerUnary : UnaryHistory nextLedger :=
    unary_cont_closed laterWindowUnary RUnary ledgerRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed ledgerUnary QUnary readbackRoute
  exact
    ⟨earlierUnary, laterUnary, earlierWindowUnary, laterWindowUnary, ledgerUnary,
      readbackUnary, earlierRoute, laterRoute, earlierWindowRoute, laterWindowRoute,
      ledgerRoute, readbackRoute, carrierPkg, readbackPkg⟩

theorem BolzanoWeierstrassCarrier_cofinal_window_extraction
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N earlierCell laterCell earlierWindow laterWindow nextLedger
      readback cofinalWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K earlierCell ->
        Cont earlierCell K laterCell ->
          Cont earlierCell S earlierWindow ->
            Cont laterCell S laterWindow ->
              Cont laterWindow R nextLedger ->
                Cont nextLedger Q readback ->
                  Cont readback Q cofinalWindow ->
                    PkgSig bundle cofinalWindow pkg ->
                      UnaryHistory earlierCell ∧ UnaryHistory laterCell ∧
                        UnaryHistory earlierWindow ∧ UnaryHistory laterWindow ∧
                          UnaryHistory nextLedger ∧ UnaryHistory readback ∧
                            UnaryHistory cofinalWindow ∧ Cont S K earlierCell ∧
                              Cont earlierCell K laterCell ∧
                                Cont earlierCell S earlierWindow ∧
                                  Cont laterCell S laterWindow ∧
                                    Cont laterWindow R nextLedger ∧
                                      Cont nextLedger Q readback ∧
                                        Cont readback Q cofinalWindow ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle cofinalWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier earlierRoute laterRoute earlierWindowRoute laterWindowRoute
    ledgerRoute readbackRoute cofinalRoute cofinalPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have earlierUnary : UnaryHistory earlierCell :=
    unary_cont_closed SUnary KUnary earlierRoute
  have laterUnary : UnaryHistory laterCell :=
    unary_cont_closed earlierUnary KUnary laterRoute
  have earlierWindowUnary : UnaryHistory earlierWindow :=
    unary_cont_closed earlierUnary SUnary earlierWindowRoute
  have laterWindowUnary : UnaryHistory laterWindow :=
    unary_cont_closed laterUnary SUnary laterWindowRoute
  have ledgerUnary : UnaryHistory nextLedger :=
    unary_cont_closed laterWindowUnary RUnary ledgerRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed ledgerUnary QUnary readbackRoute
  have cofinalUnary : UnaryHistory cofinalWindow :=
    unary_cont_closed readbackUnary QUnary cofinalRoute
  exact
    ⟨earlierUnary, laterUnary, earlierWindowUnary, laterWindowUnary, ledgerUnary,
      readbackUnary, cofinalUnary, earlierRoute, laterRoute, earlierWindowRoute,
      laterWindowRoute, ledgerRoute, readbackRoute, cofinalRoute, carrierPkg,
      cofinalPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
