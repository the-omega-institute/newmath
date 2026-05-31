import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_monotone_window_regularity [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow scheduleRead regularRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedWindow ->
        Cont retainedWindow Q scheduleRead ->
          Cont scheduleRead H regularRead ->
            Cont regularRead C transportedRead ->
              PkgSig bundle transportedRead pkg ->
                UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                  UnaryHistory retainedWindow ∧ UnaryHistory scheduleRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory transportedRead ∧
                      Cont K R retainedWindow ∧ Cont retainedWindow Q scheduleRead ∧
                        Cont scheduleRead H regularRead ∧ Cont regularRead C transportedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier retainedRoute scheduleRoute regularRoute transportedRoute transportedPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, _EUnary, HUnary, CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed retainedUnary QUnary scheduleRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleUnary HUnary regularRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed regularUnary CUnary transportedRoute
  exact
    ⟨KUnary, RUnary, QUnary, retainedUnary, scheduleUnary, regularUnary, transportedUnary,
      retainedRoute, scheduleRoute, regularRoute, transportedRoute, carrierPkg,
      transportedPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
