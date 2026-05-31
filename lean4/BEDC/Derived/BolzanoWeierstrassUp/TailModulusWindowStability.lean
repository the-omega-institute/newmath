import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_tail_modulus_window_stability
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedCell meshModulus transportedModulus readbackWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedCell ->
        Cont retainedCell H meshModulus ->
          Cont meshModulus C transportedModulus ->
            Cont transportedModulus Q readbackWindow ->
              PkgSig bundle readbackWindow pkg ->
                UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧
                  UnaryHistory Q ∧ UnaryHistory retainedCell ∧ UnaryHistory meshModulus ∧
                    UnaryHistory transportedModulus ∧ UnaryHistory readbackWindow ∧
                      Cont K R retainedCell ∧ Cont retainedCell H meshModulus ∧
                        Cont meshModulus C transportedModulus ∧
                          Cont transportedModulus Q readbackWindow ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle readbackWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier retainedRoute meshRoute transportRoute readbackRoute readbackPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, _EUnary, HUnary, CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed KUnary RUnary retainedRoute
  have meshUnary : UnaryHistory meshModulus :=
    unary_cont_closed retainedUnary HUnary meshRoute
  have transportedUnary : UnaryHistory transportedModulus :=
    unary_cont_closed meshUnary CUnary transportRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed transportedUnary QUnary readbackRoute
  exact
    ⟨KUnary, RUnary, HUnary, CUnary, QUnary, retainedUnary, meshUnary, transportedUnary,
      readbackUnary, retainedRoute, meshRoute, transportRoute, readbackRoute, carrierPkg,
      readbackPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
