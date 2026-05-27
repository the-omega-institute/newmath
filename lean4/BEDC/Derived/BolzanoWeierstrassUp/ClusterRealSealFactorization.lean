import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cluster_real_seal_factorization [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree extracted readback cluster realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalTree ->
        Cont intervalTree R extracted ->
          Cont extracted Q readback ->
            Cont readback E cluster ->
              Cont cluster H realSealRead ->
                PkgSig bundle realSealRead pkg ->
                  UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory intervalTree ∧
                      UnaryHistory extracted ∧ UnaryHistory readback ∧ UnaryHistory cluster ∧
                        UnaryHistory realSealRead ∧ Cont S K intervalTree ∧
                          Cont intervalTree R extracted ∧ Cont extracted Q readback ∧
                            Cont readback E cluster ∧ Cont cluster H realSealRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier intervalRoute extractedRoute readbackRoute clusterRoute realSealRoute
    realSealPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed SUnary KUnary intervalRoute
  have extractedUnary : UnaryHistory extracted :=
    unary_cont_closed intervalUnary RUnary extractedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed extractedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed clusterUnary HUnary realSealRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, intervalUnary, extractedUnary,
      readbackUnary, clusterUnary, realSealUnary, intervalRoute, extractedRoute,
      readbackRoute, clusterRoute, realSealRoute, carrierPkg, realSealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
