import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_public_cluster_export [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceRead extractionRead clusterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceRead ->
        Cont sourceRead R extractionRead ->
          Cont extractionRead Q clusterRead ->
            PkgSig bundle clusterRead pkg ->
              UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                UnaryHistory E ∧ UnaryHistory sourceRead ∧ UnaryHistory extractionRead ∧
                  UnaryHistory clusterRead ∧ Cont S K sourceRead ∧
                    Cont sourceRead R extractionRead ∧
                      Cont extractionRead Q clusterRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle clusterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceRoute extractionRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed SUnary KUnary sourceRoute
  have extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed sourceUnary RUnary extractionRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed extractionUnary QUnary clusterRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, sourceUnary, extractionUnary,
      clusterUnary, sourceRoute, extractionRoute, clusterRoute, carrierPkg, clusterPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
