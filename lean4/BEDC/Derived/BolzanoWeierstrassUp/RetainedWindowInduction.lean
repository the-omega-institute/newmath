import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_retained_window_induction [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow readbackWindow dyadicTolerance realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedWindow ->
        Cont retainedWindow Q readbackWindow ->
          Cont readbackWindow H dyadicTolerance ->
            Cont dyadicTolerance E realSeal ->
              PkgSig bundle realSeal pkg ->
                UnaryHistory retainedWindow ∧ UnaryHistory readbackWindow ∧
                  UnaryHistory dyadicTolerance ∧ UnaryHistory realSeal ∧
                    Cont K R retainedWindow ∧ Cont retainedWindow Q readbackWindow ∧
                      Cont readbackWindow H dyadicTolerance ∧
                        Cont dyadicTolerance E realSeal ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BolzanoWeierstrassCarrier BHist Cont PkgSig UnaryHistory
  intro carrier retainedRoute readbackRoute dyadicRoute realSealRoute realSealPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    _carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have dyadicUnary : UnaryHistory dyadicTolerance :=
    unary_cont_closed readbackUnary HUnary dyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary EUnary realSealRoute
  exact
    ⟨retainedUnary, readbackUnary, dyadicUnary, realSealUnary, retainedRoute,
      readbackRoute, dyadicRoute, realSealRoute, realSealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
