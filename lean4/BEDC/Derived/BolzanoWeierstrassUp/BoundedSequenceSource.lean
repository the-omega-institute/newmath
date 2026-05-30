import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_bounded_sequence_source [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S Q sourceRead ->
        Cont sourceRead K windowRead ->
          PkgSig bundle windowRead pkg ->
            UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory K ∧ UnaryHistory sourceRead ∧
              UnaryHistory windowRead ∧ Cont S Q sourceRead ∧
                Cont sourceRead K windowRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceRoute windowRoute windowPkg
  obtain ⟨SUnary, KUnary, _RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed SUnary QUnary sourceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary KUnary windowRoute
  exact
    ⟨SUnary, QUnary, KUnary, sourceUnary, windowUnary, sourceRoute, windowRoute,
      carrierPkg, windowPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
