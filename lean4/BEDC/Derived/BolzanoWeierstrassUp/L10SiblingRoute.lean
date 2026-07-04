import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_l10_sibling_route [AskSetup] [PackageSetup]
    {S K R Q E H C P N compactMetricRow streamWindow regSeqRead dyadicTolerance
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K compactMetricRow ->
        Cont compactMetricRow R streamWindow ->
          Cont streamWindow Q regSeqRead ->
            Cont regSeqRead H dyadicTolerance ->
              Cont dyadicTolerance E realSeal ->
                PkgSig bundle realSeal pkg ->
                  UnaryHistory compactMetricRow ∧ UnaryHistory streamWindow ∧
                    UnaryHistory regSeqRead ∧ UnaryHistory dyadicTolerance ∧
                      UnaryHistory realSeal ∧ Cont S K compactMetricRow ∧
                        Cont compactMetricRow R streamWindow ∧
                          Cont streamWindow Q regSeqRead ∧
                            Cont regSeqRead H dyadicTolerance ∧
                              Cont dyadicTolerance E realSeal ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier compactMetricRoute streamRoute regSeqRoute dyadicRoute realRoute realPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have compactMetricUnary : UnaryHistory compactMetricRow :=
    unary_cont_closed SUnary KUnary compactMetricRoute
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed compactMetricUnary RUnary streamRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamUnary QUnary regSeqRoute
  have dyadicUnary : UnaryHistory dyadicTolerance :=
    unary_cont_closed regSeqUnary HUnary dyadicRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary EUnary realRoute
  exact
    ⟨compactMetricUnary, streamUnary, regSeqUnary, dyadicUnary, realUnary,
      compactMetricRoute, streamRoute, regSeqRoute, dyadicRoute, realRoute,
      carrierPkg, realPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
