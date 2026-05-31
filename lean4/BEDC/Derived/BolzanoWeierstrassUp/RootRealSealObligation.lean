import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassRootRealSealObligation [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree extracted realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R intervalTree ->
        Cont intervalTree Q extracted ->
          Cont extracted E realSealRead ->
            PkgSig bundle realSealRead pkg ->
              UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                UnaryHistory intervalTree ∧ UnaryHistory extracted ∧
                  UnaryHistory realSealRead ∧ Cont K R intervalTree ∧
                    Cont intervalTree Q extracted ∧ Cont extracted E realSealRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier intervalRoute extractionRoute sealRoute sealPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    provenancePkg⟩ := carrier
  have intervalTreeUnary : UnaryHistory intervalTree :=
    unary_cont_closed KUnary RUnary intervalRoute
  have extractedUnary : UnaryHistory extracted :=
    unary_cont_closed intervalTreeUnary QUnary extractionRoute
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed extractedUnary EUnary sealRoute
  exact
    ⟨KUnary, RUnary, QUnary, EUnary, intervalTreeUnary, extractedUnary, realSealReadUnary,
      intervalRoute, extractionRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
