import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow regseqRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedWindow ->
        Cont R Q regseqRead ->
          Cont regseqRead E realSealRead ->
            PkgSig bundle realSealRead pkg ->
              UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                UnaryHistory retainedWindow ∧ UnaryHistory regseqRead ∧
                  UnaryHistory realSealRead ∧ Cont K R retainedWindow ∧
                    Cont R Q regseqRead ∧ Cont regseqRead E realSealRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier retainedRoute regseqRoute sealRoute sealPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed RUnary QUnary regseqRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed regseqUnary EUnary sealRoute
  exact
    ⟨KUnary, RUnary, QUnary, EUnary, retainedUnary, regseqUnary, realSealUnary,
      retainedRoute, regseqRoute, sealRoute, carrierPkg, sealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
