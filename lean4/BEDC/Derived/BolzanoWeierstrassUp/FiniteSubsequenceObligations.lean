import BEDC.Derived.BolzanoWeierstrassUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BolzanoWeierstrassCarrier [AskSetup] [PackageSetup]
    (S K R Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S K R ∧ Cont R Q E ∧ Cont H C P ∧ PkgSig bundle P pkg

theorem BolzanoWeierstrassCarrier_finite_subsequence_obligations [AskSetup] [PackageSetup]
    {S K R Q E H C P N subseqRead clusterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R subseqRead ->
        Cont subseqRead Q clusterRead ->
          PkgSig bundle clusterRead pkg ->
            UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
              UnaryHistory subseqRead ∧ UnaryHistory clusterRead ∧ Cont K R subseqRead ∧
                Cont subseqRead Q clusterRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle clusterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier subseqRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have subseqUnary : UnaryHistory subseqRead :=
    unary_cont_closed KUnary RUnary subseqRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed subseqUnary QUnary clusterRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, subseqUnary, clusterUnary, subseqRoute,
      clusterRoute, carrierPkg, clusterPkg⟩

theorem BolzanoWeierstrassPublicSubsequenceSelector [AskSetup] [PackageSetup]
    {S K R Q E H C P N selector : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K selector ->
        Cont selector R Q ->
          UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
            UnaryHistory selector ∧ Cont S K selector ∧ Cont selector R Q ∧
              PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorRoute readbackRoute
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed SUnary KUnary selectorRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, selectorUnary, selectorRoute, readbackRoute,
      carrierPkg⟩

theorem BolzanoWeierstrassPublicClusterWitness [AskSetup] [PackageSetup]
    {S K R Q E H C P N selector cluster : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K selector ->
        Cont selector R Q ->
          Cont Q E cluster ->
            UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
              UnaryHistory E ∧ UnaryHistory selector ∧ UnaryHistory cluster ∧
                Cont S K selector ∧ Cont selector R Q ∧ Cont Q E cluster ∧
                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorRoute readbackRoute clusterRoute
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed SUnary KUnary selectorRoute
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed QUnary EUnary clusterRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, selectorUnary, clusterUnary,
      selectorRoute, readbackRoute, clusterRoute, carrierPkg⟩

theorem BolzanoWeierstrassCarrier_root_subsequence_extraction_obligation
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree extracted readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalTree ->
        Cont intervalTree R extracted ->
          Cont extracted Q readback ->
            PkgSig bundle readback pkg ->
              UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                UnaryHistory intervalTree ∧ UnaryHistory extracted ∧ UnaryHistory readback ∧
                  Cont S K intervalTree ∧ Cont intervalTree R extracted ∧
                    Cont extracted Q readback ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
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
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, intervalUnary, extractedUnary, readbackUnary,
      intervalRoute, extractionRoute, readbackRoute, carrierPkg, readbackPkg⟩

theorem BolzanoWeierstrassPublicNonescapePackage [AskSetup] [PackageSetup]
    {S K R Q E H C P N selector cluster publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K selector ->
        Cont selector R Q ->
          Cont Q E cluster ->
            Cont cluster H publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                  UnaryHistory E ∧ UnaryHistory selector ∧ UnaryHistory cluster ∧
                    UnaryHistory publicRead ∧ Cont S K selector ∧ Cont selector R Q ∧
                      Cont Q E cluster ∧ Cont cluster H publicRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorRoute readbackRoute clusterRoute publicRoute publicPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed SUnary KUnary selectorRoute
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed QUnary EUnary clusterRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed clusterUnary HUnary publicRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, selectorUnary, clusterUnary,
      publicReadUnary, selectorRoute, readbackRoute, clusterRoute, publicRoute,
      carrierPkg, publicPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
