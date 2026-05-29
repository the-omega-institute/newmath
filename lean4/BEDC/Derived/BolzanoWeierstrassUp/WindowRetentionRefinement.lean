import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_window_retention_refinement [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow readbackWindow sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      Cont K R retainedWindow →
        Cont retainedWindow Q readbackWindow →
          Cont readbackWindow E sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                UnaryHistory E ∧ UnaryHistory retainedWindow ∧
                  UnaryHistory readbackWindow ∧ UnaryHistory sealRead ∧
                    Cont K R retainedWindow ∧ Cont retainedWindow Q readbackWindow ∧
                      Cont readbackWindow E sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier retainedRoute readbackRoute sealRoute sealPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary EUnary sealRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, retainedUnary, readbackUnary,
      sealUnary, retainedRoute, readbackRoute, sealRoute, carrierPkg, sealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
