import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_regular_subsequence_window_readback
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree extracted readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      Cont S K intervalTree →
        Cont intervalTree R extracted →
          Cont extracted Q readback →
            PkgSig bundle readback pkg →
              ∃ windowRead : BHist,
                UnaryHistory windowRead ∧
                  hsame windowRead (append (append intervalTree extracted) readback) ∧
                    Cont S K intervalTree ∧
                      Cont intervalTree R extracted ∧
                        Cont extracted Q readback ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier intervalRoute extractionRoute readbackRoute readbackPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed SUnary KUnary intervalRoute
  have extractedUnary : UnaryHistory extracted :=
    unary_cont_closed intervalUnary RUnary extractionRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed extractedUnary QUnary readbackRoute
  have intervalExtractedUnary : UnaryHistory (append intervalTree extracted) :=
    unary_append_closed intervalUnary extractedUnary
  exact
    ⟨append (append intervalTree extracted) readback,
      unary_append_closed intervalExtractedUnary readbackUnary,
      hsame_refl (append (append intervalTree extracted) readback), intervalRoute,
      extractionRoute, readbackRoute, carrierPkg, readbackPkg⟩

theorem BolzanoWeierstrassCarrier_regular_cauchy_subsequence_readback
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree retainedWindow readbackWindow clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalTree ->
        Cont K R retainedWindow ->
          Cont retainedWindow Q readbackWindow ->
            Cont readbackWindow E clusterSeal ->
              PkgSig bundle clusterSeal pkg ->
                UnaryHistory intervalTree ∧ UnaryHistory retainedWindow ∧
                  UnaryHistory readbackWindow ∧ UnaryHistory clusterSeal ∧
                    Cont S K intervalTree ∧ Cont K R retainedWindow ∧
                      Cont retainedWindow Q readbackWindow ∧
                        Cont readbackWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle clusterSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier intervalRoute retainedRoute readbackRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed SUnary KUnary intervalRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  exact
    ⟨intervalUnary, retainedUnary, readbackUnary, clusterUnary, intervalRoute,
      retainedRoute, readbackRoute, clusterRoute, carrierPkg, clusterPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
