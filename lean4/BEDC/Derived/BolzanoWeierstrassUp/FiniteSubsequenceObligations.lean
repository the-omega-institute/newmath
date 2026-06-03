import BEDC.Derived.BolzanoWeierstrassUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem BolzanoWeierstrassCarrier_ledger_refusal [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow readbackWindow clusterSeal consumerLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedWindow ->
        Cont retainedWindow Q readbackWindow ->
          Cont readbackWindow E clusterSeal ->
            Cont clusterSeal H consumerLedger ->
              PkgSig bundle consumerLedger pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumerLedger ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                        hsame row E ∨ hsame row retainedWindow ∨
                          hsame row readbackWindow ∨ hsame row clusterSeal ∨
                            hsame row consumerLedger)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K R retainedWindow ∧
                        Cont retainedWindow Q readbackWindow ∧
                          Cont readbackWindow E clusterSeal ∧
                            Cont clusterSeal H consumerLedger ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle consumerLedger pkg)
                    hsame ∧
                  UnaryHistory consumerLedger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier retainedRoute readbackRoute clusterRoute consumerRoute consumerPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have consumerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed clusterUnary HUnary consumerRoute
  have sourceConsumer :
      (fun row : BHist => hsame row consumerLedger ∧ UnaryHistory row) consumerLedger := by
    exact ⟨hsame_refl consumerLedger, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row E ∨
              hsame row retainedWindow ∨ hsame row readbackWindow ∨
                hsame row clusterSeal ∨ hsame row consumerLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K R retainedWindow ∧
              Cont retainedWindow Q readbackWindow ∧ Cont readbackWindow E clusterSeal ∧
                Cont clusterSeal H consumerLedger ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle consumerLedger pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerLedger sourceConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, retainedRoute, readbackRoute, clusterRoute, consumerRoute,
          carrierPkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

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

theorem BolzanoWeierstrassCarrier_bounded_subsequence_cluster_obligation
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree extracted readback cluster : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K intervalTree ->
        Cont intervalTree R extracted ->
          Cont extracted Q readback ->
            Cont readback E cluster ->
              PkgSig bundle cluster pkg ->
                UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                  UnaryHistory E ∧ UnaryHistory intervalTree ∧ UnaryHistory extracted ∧
                    UnaryHistory readback ∧ UnaryHistory cluster ∧ Cont S K intervalTree ∧
                      Cont intervalTree R extracted ∧ Cont extracted Q readback ∧
                        Cont readback E cluster ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle cluster pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier intervalRoute extractionRoute readbackRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed SUnary KUnary intervalRoute
  have extractedUnary : UnaryHistory extracted :=
    unary_cont_closed intervalUnary RUnary extractionRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed extractedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, intervalUnary, extractedUnary,
      readbackUnary, clusterUnary, intervalRoute, extractionRoute, readbackRoute,
      clusterRoute, carrierPkg, clusterPkg⟩

theorem BolzanoWeierstrassCarrier_bounded_source_factorization [AskSetup] [PackageSetup]
    {S K R Q E H C P N boundedSource intervalTree extracted readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S H boundedSource ->
        Cont boundedSource K intervalTree ->
          Cont intervalTree R extracted ->
            Cont extracted Q readback ->
              PkgSig bundle readback pkg ->
                UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                  UnaryHistory H ∧ UnaryHistory boundedSource ∧ UnaryHistory intervalTree ∧
                    UnaryHistory extracted ∧ UnaryHistory readback ∧ Cont S H boundedSource ∧
                      Cont boundedSource K intervalTree ∧ Cont intervalTree R extracted ∧
                        Cont extracted Q readback ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier boundedRoute intervalRoute extractionRoute readbackRoute readbackPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have boundedUnary : UnaryHistory boundedSource :=
    unary_cont_closed SUnary HUnary boundedRoute
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed boundedUnary KUnary intervalRoute
  have extractedUnary : UnaryHistory extracted :=
    unary_cont_closed intervalUnary RUnary extractionRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed extractedUnary QUnary readbackRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, HUnary, boundedUnary, intervalUnary,
      extractedUnary, readbackUnary, boundedRoute, intervalRoute, extractionRoute,
      readbackRoute, carrierPkg, readbackPkg⟩

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

theorem BolzanoWeierstrassCarrier_bounded_cluster_route [AskSetup] [PackageSetup]
    {S K R Q E H C P N boundedSource intervalTree extracted readback cluster publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S H boundedSource ->
        Cont boundedSource K intervalTree ->
          Cont intervalTree R extracted ->
            Cont extracted Q readback ->
              Cont readback E cluster ->
                Cont cluster C publicRead ->
                  PkgSig bundle publicRead pkg ->
                    UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                      UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                        UnaryHistory boundedSource ∧ UnaryHistory intervalTree ∧
                          UnaryHistory extracted ∧ UnaryHistory readback ∧
                            UnaryHistory cluster ∧ UnaryHistory publicRead ∧
                              Cont S H boundedSource ∧ Cont boundedSource K intervalTree ∧
                                Cont intervalTree R extracted ∧ Cont extracted Q readback ∧
                                  Cont readback E cluster ∧ Cont cluster C publicRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier boundedRoute intervalRoute extractionRoute readbackRoute clusterRoute
    publicRoute publicPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have boundedUnary : UnaryHistory boundedSource :=
    unary_cont_closed SUnary HUnary boundedRoute
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed boundedUnary KUnary intervalRoute
  have extractedUnary : UnaryHistory extracted :=
    unary_cont_closed intervalUnary RUnary extractionRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed extractedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed clusterUnary CUnary publicRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, CUnary, boundedUnary,
      intervalUnary, extractedUnary, readbackUnary, clusterUnary, publicUnary,
      boundedRoute, intervalRoute, extractionRoute, readbackRoute, clusterRoute,
      publicRoute, carrierPkg, publicPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
