import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZetaContinuationWitnessPacket [AskSetup] [PackageSetup]
    (basic eta analytic pole functional zeroLedger gamma transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont basic eta analytic ∧
    Cont analytic functional transports ∧
    Cont pole zeroLedger gamma ∧
    Cont transports routes provenance ∧
    PkgSig bundle name pkg ∧
    PkgSig bundle provenance pkg

theorem ZetaContinuationWitnessPacket_dependency_ledger [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
      provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont transports' routes provenance' →
      PkgSig bundle provenance' pkg →
      hsame eta eta' →
      hsame analytic analytic' /\ hsame transports transports' /\
        hsame provenance provenance' /\ PkgSig bundle name pkg /\
          PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  cases packet with
  | intro basicAnalytic rest =>
      cases rest with
      | intro analyticTransport rest =>
          cases rest with
          | intro _functionalGamma rest =>
              cases rest with
              | intro transportProvenance rest =>
                  cases rest with
                  | intro namePkg _provenancePkg =>
                      have analyticSame : hsame analytic analytic' :=
                        cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
                      have transportsSame : hsame transports transports' :=
                        cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport
                          functionalRoute
                      have provenanceSame : hsame provenance provenance' :=
                        cont_respects_hsame transportsSame (hsame_refl routes) transportProvenance
                          provenanceRoute
                      exact
                        ⟨analyticSame, transportsSame, provenanceSame, namePkg,
                          provenancePkg⟩

theorem ZetaContinuationWitnessPacket_public_export [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name exportRow →
            UnaryHistory exportRow ∧ hsame exportRow (append routes name) ∧
              PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameExport
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  exact ⟨exportUnary, routesNameExport, namePkg, provenancePkg⟩

theorem ZetaContinuationWitnessPacket_public_source_lock_handoff [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' exportRow exportRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont transports' routes provenance' →
            Cont routes name exportRow →
              Cont routes name exportRow' →
                PkgSig bundle provenance' pkg →
                  hsame eta eta' →
                    hsame analytic analytic' ∧ hsame transports transports' ∧
                      hsame provenance provenance' ∧ hsame exportRow exportRow' ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet basicRoute functionalRoute provenanceRoute exportRoute exportRoute'
    provenancePkg etaSame
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have exportSame : hsame exportRow exportRow' :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) exportRoute exportRoute'
  exact
    ⟨analyticSame, transportsSame, provenanceSame, exportSame, namePkg, provenancePkg'⟩

theorem ZetaContinuationWitnessPacket_source_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      hsame eta eta' →
      hsame analytic analytic' ∧ hsame transports transports' ∧ PkgSig bundle name pkg ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet basicRoute functionalRoute etaSame
  obtain ⟨basicAnalytic, analyticTransport, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport functionalRoute
  exact ⟨analyticSame, transportsSame, namePkg, provenancePkg⟩

theorem ZetaContinuationWitnessPacket_gamma_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg →
      Cont pole zeroLedger' gamma' →
      hsame zeroLedger zeroLedger' →
      hsame gamma gamma' ∧ PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet gammaRoute zeroLedgerSame
  obtain ⟨_basicAnalytic, _analyticTransport, poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have gammaSame : hsame gamma gamma' :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleGamma gammaRoute
  exact ⟨gammaSame, namePkg, provenancePkg⟩

theorem ZetaContinuationWitnessPacket_zero_facing_source_totality [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
      provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont transports' routes provenance' →
      PkgSig bundle provenance' pkg →
      hsame eta eta' →
      UnaryHistory routes →
      UnaryHistory name →
      Cont routes name exportRow →
      hsame analytic analytic' ∧ hsame transports transports' ∧ hsame provenance provenance' ∧
        UnaryHistory exportRow ∧ hsame exportRow (append routes name) ∧
          PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame routesUnary
    nameUnary routesNameExport
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  exact
    ⟨analyticSame, transportsSame, provenanceSame, exportUnary, routesNameExport, namePkg,
      provenancePkg'⟩

theorem ZetaContinuationWitnessPacket_eta_pole_functional_readiness [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' zeroLedger' gamma' exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
      provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont pole zeroLedger' gamma' →
      hsame eta eta' →
      hsame zeroLedger zeroLedger' →
      UnaryHistory routes →
      UnaryHistory name →
      Cont routes name exportRow →
      hsame analytic analytic' ∧ hsame transports transports' ∧ hsame gamma gamma' ∧
        UnaryHistory exportRow ∧ hsame exportRow (append routes name) ∧
          PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute gammaRoute etaSame zeroLedgerSame routesUnary
    nameUnary routesNameExport
  have source :=
    ZetaContinuationWitnessPacket_source_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (bundle := bundle) (pkg := pkg)
      packet basicRoute functionalRoute etaSame
  obtain ⟨analyticSame, transportsSame, namePkg, provenancePkg⟩ := source
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, _namePkg', _provenancePkg'⟩ := gammaBoundary
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  exact
    ⟨analyticSame, transportsSame, gammaSame, exportUnary, routesNameExport, namePkg,
      provenancePkg⟩

theorem ZetaContinuationWitnessPacket_root_readiness_lock [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont transports' routes provenance' →
      Cont pole zeroLedger' gamma' →
      PkgSig bundle provenance' pkg →
      hsame eta eta' →
      hsame zeroLedger zeroLedger' →
      UnaryHistory routes →
      UnaryHistory name →
      Cont routes name rootRead →
      hsame analytic analytic' ∧ hsame transports transports' ∧ hsame provenance provenance' ∧
        hsame gamma gamma' ∧ UnaryHistory rootRead ∧ hsame rootRead (append routes name) ∧
          PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNameRootRead
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, _namePkgGamma, _provenancePkgGamma⟩ := gammaBoundary
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routesUnary nameUnary routesNameRootRead
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, rootReadUnary,
      routesNameRootRead, namePkg, provenancePkg'⟩

theorem ZetaContinuationWitnessPacket_public_root_export [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name rootRead ->
            PkgSig bundle rootRead pkg ->
              UnaryHistory rootRead /\ hsame rootRead (append routes name) /\
                Cont basic eta analytic /\ Cont analytic functional transports /\
                  Cont pole zeroLedger gamma /\ Cont transports routes provenance /\
                    PkgSig bundle name pkg /\ PkgSig bundle provenance pkg /\
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameRootRead rootReadPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routesUnary nameUnary routesNameRootRead
  exact
    ⟨rootReadUnary, routesNameRootRead, basicEtaAnalytic, analyticFunctionalTransports,
      poleZeroLedgerGamma, transportsRoutesProvenance, namePkg, provenancePkg, rootReadPkg⟩

theorem ZetaContinuationWitnessPacket_critical_strip_root_handoff [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' publicRoot : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont transports' routes provenance' ->
            Cont pole zeroLedger' gamma' ->
              PkgSig bundle provenance' pkg ->
                hsame eta eta' ->
                  hsame zeroLedger zeroLedger' ->
                    UnaryHistory routes ->
                      UnaryHistory name ->
                        Cont routes name publicRoot ->
                          PkgSig bundle publicRoot pkg ->
                            SemanticNameCert
                              (fun row : BHist =>
                                ZetaContinuationWitnessPacket basic eta analytic pole
                                  functional zeroLedger gamma transports routes provenance name
                                  bundle pkg /\ hsame row gamma)
                              (fun row : BHist => hsame row gamma /\ UnaryHistory publicRoot)
                              (fun row : BHist =>
                                PkgSig bundle provenance' pkg /\
                                  PkgSig bundle publicRoot pkg /\ hsame row gamma /\
                                    Cont pole zeroLedger' gamma')
                              hsame /\
                            hsame analytic analytic' /\ hsame transports transports' /\
                              hsame provenance provenance' /\ hsame gamma gamma' /\
                                UnaryHistory publicRoot /\
                                  hsame publicRoot (append routes name) /\
                                    PkgSig bundle name pkg /\
                                      PkgSig bundle provenance' pkg /\
                                        PkgSig bundle publicRoot pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNamePublic publicRootPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := publicRoot)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary routesNamePublic
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, publicRootUnary,
    publicRootSame, namePkg, provenancePkg'⟩ := readiness
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
            transports routes provenance name bundle pkg /\ hsame row gamma)
        (fun row : BHist => hsame row gamma /\ UnaryHistory publicRoot)
        (fun row : BHist =>
          PkgSig bundle provenance' pkg /\ PkgSig bundle publicRoot pkg /\
            hsame row gamma /\ Cont pole zeroLedger' gamma')
        hsame := by
    constructor
    · constructor
      · exact Exists.intro gamma ⟨packet, hsame_refl gamma⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, publicRootUnary⟩
    · intro row source
      exact ⟨provenancePkg', publicRootPkg, source.right, gammaRoute⟩
  exact
    ⟨cert, analyticSame, transportsSame, provenanceSame, gammaSame, publicRootUnary,
      publicRootSame, namePkg, provenancePkg', publicRootPkg⟩

theorem ZetaContinuationWitnessPacket_public_export_totality [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' publicRoot publicRoot' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont transports' routes provenance' →
      Cont pole zeroLedger' gamma' →
      PkgSig bundle provenance' pkg →
      hsame eta eta' →
      hsame zeroLedger zeroLedger' →
      UnaryHistory routes →
      UnaryHistory name →
      Cont routes name publicRoot →
      Cont routes name publicRoot' →
      PkgSig bundle publicRoot pkg →
      PkgSig bundle publicRoot' pkg →
      hsame analytic analytic' ∧ hsame transports transports' ∧ hsame provenance provenance' ∧
        hsame gamma gamma' ∧ hsame publicRoot publicRoot' ∧ UnaryHistory publicRoot ∧
          UnaryHistory publicRoot' ∧ hsame publicRoot (append routes name) ∧
            hsame publicRoot' (append routes name) ∧ PkgSig bundle name pkg ∧
              PkgSig bundle provenance' pkg ∧ PkgSig bundle publicRoot pkg ∧
                PkgSig bundle publicRoot' pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary publicRoute publicRoute' publicRootPkg publicRootPkg'
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := publicRoot)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary publicRoute
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, publicRootUnary,
    publicRootSame, namePkg, provenancePkg'⟩ := readiness
  have publicRootUnary' : UnaryHistory publicRoot' :=
    unary_cont_closed routesUnary nameUnary publicRoute'
  have publicRootSame' : hsame publicRoot' (append routes name) :=
    publicRoute'
  have publicRootsSame : hsame publicRoot publicRoot' :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) publicRoute publicRoute'
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, publicRootsSame,
      publicRootUnary, publicRootUnary', publicRootSame, publicRootSame', namePkg,
      provenancePkg', publicRootPkg, publicRootPkg'⟩

end BEDC.Derived.ZetaContinuationWitnessUp
