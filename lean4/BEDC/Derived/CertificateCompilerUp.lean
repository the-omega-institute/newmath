import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CertificateCompilerCarrier [AskSetup] [PackageSetup]
    (source target graph landing routes transport provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧ UnaryHistory landing ∧
    UnaryHistory routes ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont source graph landing ∧ Cont landing routes target ∧ Cont provenance target cert ∧
        hsame cert (append provenance target) ∧ PkgSig bundle cert pkg

def CertificateCompilerClassifier [AskSetup] [PackageSetup]
    (source target graph landing routes transport provenance cert edge edge' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CertificateCompilerCarrier source target graph landing routes transport provenance cert
      bundle pkg ∧
    UnaryHistory edge ∧ UnaryHistory edge' ∧ hsame edge edge' ∧
      Cont graph edge landing ∧ Cont graph edge' landing ∧ Cont landing routes target

theorem CertificateCompilerClassifier_displayed_edge_witness_totality [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory edge ∧ UnaryHistory edge' ∧
        hsame edge edge' ∧ Cont source graph landing ∧ Cont graph edge landing ∧
          Cont graph edge' landing ∧ Cont landing routes target ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro classifier
  obtain ⟨carrier, edgeUnary, edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  exact
    ⟨graphUnary, landingUnary, edgeUnary, edgeUnary', edgeSame, sourceGraphLanding,
      graphEdgeLanding, graphEdgeLanding', landingRoutesTarget', certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_consumer_replay_obligation_triad [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' replay certEndpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      Cont landing routes replay ->
        hsame cert certEndpoint ->
          PkgSig bundle certEndpoint pkg ->
            UnaryHistory graph ∧ UnaryHistory landing ∧ UnaryHistory replay ∧
              hsame edge edge' ∧ Cont graph edge landing ∧ Cont graph edge' landing ∧
                Cont landing routes target ∧ Cont landing routes replay ∧
                  hsame certEndpoint (append provenance target) ∧
                    PkgSig bundle certEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro classifier landingRoutesReplay certEndpointSame certEndpointPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed landingUnary routesUnary landingRoutesReplay
  have certEndpointMatches : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact
    ⟨graphUnary, landingUnary, replayUnary, edgeSame, graphEdgeLanding,
      graphEdgeLanding', landingRoutesTarget', landingRoutesReplay, certEndpointMatches,
      certEndpointPkg⟩

theorem CertificateCompilerCarrier_target_endpoint_route [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert targetEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame targetEndpoint target ->
        UnaryHistory targetEndpoint ∧ UnaryHistory graph ∧ UnaryHistory landing ∧
          Cont source graph landing ∧ Cont landing routes target ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier endpointSame
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have targetEndpointUnary : UnaryHistory targetEndpoint :=
    unary_transport targetUnary (hsame_symm endpointSame)
  exact
    ⟨targetEndpointUnary, graphUnary, landingUnary, sourceGraphLanding, landingRoutesTarget,
      certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_target_endpoint_determinacy [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame endpoint target ->
        hsame endpoint' target ->
          hsame endpoint endpoint' ∧ UnaryHistory endpoint ∧ UnaryHistory endpoint' ∧
            Cont source graph landing ∧ Cont landing routes target ∧
              hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier endpointSame endpointSame'
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpoint' :=
    hsame_trans endpointSame (hsame_symm endpointSame')
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport targetUnary (hsame_symm endpointSame)
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport targetUnary (hsame_symm endpointSame')
  exact
    ⟨endpointDeterminacy, endpointUnary, endpointUnary', sourceGraphLanding,
      landingRoutesTarget, certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_root_classifier_transport_obligation [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert targetTransport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      Cont graph transport targetTransport ->
        UnaryHistory transport ∧ UnaryHistory targetTransport ∧
          Cont graph transport targetTransport ∧ Cont landing routes target ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier graphTransportTarget
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, _landingUnary, _routesUnary,
    transportUnary, _provenanceUnary, _sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have targetTransportUnary : UnaryHistory targetTransport :=
    unary_cont_closed graphUnary transportUnary graphTransportTarget
  exact
    ⟨transportUnary, targetTransportUnary, graphTransportTarget, landingRoutesTarget,
      certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_root_landing_obligation [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame landingRead landing ->
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
          UnaryHistory landingRead ∧ Cont source graph landing ∧
            hsame cert (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier landingSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_transport_symm landingUnary landingSame
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingReadUnary, sourceGraphLanding,
      certMatchesEndpoint, certPkg⟩

theorem CertificateCompilerCarrier_bridge_rows_nonescape [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert targetEndpoint certEndpoint :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame targetEndpoint target ->
        hsame cert certEndpoint ->
          UnaryHistory targetEndpoint ∧ UnaryHistory graph ∧ UnaryHistory landing ∧
            UnaryHistory routes ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
              UnaryHistory certEndpoint ∧ Cont source graph landing ∧
                Cont landing routes target ∧ Cont provenance target cert ∧
                  hsame certEndpoint (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier endpointSame certEndpointSame
  obtain ⟨_sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have targetEndpointUnary : UnaryHistory targetEndpoint :=
    unary_transport targetUnary (hsame_symm endpointSame)
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have certEndpointUnary : UnaryHistory certEndpoint :=
    unary_transport certUnary certEndpointSame
  have certEndpointMatches : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact
    ⟨targetEndpointUnary, graphUnary, landingUnary, routesUnary, transportUnary,
      provenanceUnary, certEndpointUnary, sourceGraphLanding, landingRoutesTarget,
        provenanceTargetCert, certEndpointMatches, certPkg⟩

theorem CertificateCompilerCarrier_root_continuation_route_obligation [AskSetup]
    [PackageSetup]
    {source target graph landing routes transport provenance cert routeEndpoint certEndpoint :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame routes routeEndpoint ->
        hsame cert certEndpoint ->
          UnaryHistory routeEndpoint ∧ UnaryHistory certEndpoint ∧
            Cont landing routes target ∧ Cont provenance target cert ∧
              hsame certEndpoint (append provenance target) ∧ PkgSig bundle cert pkg := by
  intro carrier routeEndpointSame certEndpointSame
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have routeEndpointUnary : UnaryHistory routeEndpoint :=
    unary_transport routesUnary routeEndpointSame
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have certEndpointUnary : UnaryHistory certEndpoint :=
    unary_transport certUnary certEndpointSame
  have certEndpointMatches : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact
    ⟨routeEndpointUnary, certEndpointUnary, landingRoutesTarget, provenanceTargetCert,
      certEndpointMatches, certPkg⟩

theorem CertificateCompilerCarrier_identity_composite_public_boundary [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget compositeTarget
      tripleTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame identityTarget source ->
        Cont target graph compositeTarget ->
          Cont compositeTarget routes tripleTarget ->
            PkgSig bundle tripleTarget pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                UnaryHistory landing ∧ UnaryHistory routes ∧ UnaryHistory identityTarget ∧
                  UnaryHistory compositeTarget ∧ UnaryHistory tripleTarget ∧
                    Cont source graph landing ∧ Cont landing routes target ∧
                      Cont target graph compositeTarget ∧
                        Cont compositeTarget routes tripleTarget ∧
                          PkgSig bundle tripleTarget pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier identitySame targetGraphComposite compositeRoutesTriple triplePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, _certMatchesEndpoint, _certPkg⟩ := carrier
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, identityUnary,
      compositeUnary, tripleUnary, sourceGraphLanding, landingRoutesTarget,
      targetGraphComposite, compositeRoutesTriple, triplePkg⟩

theorem CertificateCompilerCarrier_route_composition_exactness [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget compositeTarget
      tripleTarget certEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame identityTarget source ->
        Cont target graph compositeTarget ->
          Cont compositeTarget routes tripleTarget ->
            hsame cert certEndpoint ->
              PkgSig bundle tripleTarget pkg ->
                UnaryHistory identityTarget ∧ UnaryHistory compositeTarget ∧
                  UnaryHistory tripleTarget ∧ UnaryHistory certEndpoint ∧
                    Cont source graph landing ∧ Cont landing routes target ∧
                      Cont target graph compositeTarget ∧
                        Cont compositeTarget routes tripleTarget ∧
                          hsame certEndpoint (append provenance target) ∧
                            PkgSig bundle tripleTarget pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier identitySame targetGraphComposite compositeRoutesTriple certEndpointSame
    triplePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have certEndpointUnary : UnaryHistory certEndpoint :=
    unary_transport certUnary certEndpointSame
  have certEndpointMatches : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact
    ⟨identityUnary, compositeUnary, tripleUnary, certEndpointUnary, sourceGraphLanding,
      landingRoutesTarget, targetGraphComposite, compositeRoutesTriple, certEndpointMatches,
      triplePkg⟩

theorem CertificateCompilerCarrier_bridge_schema_handoff [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame cert bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont provenance target row ∧ Cont source graph landing ∧
              Cont landing routes target)
            (fun row : BHist => PkgSig bundle row pkg ∧ hsame row (append provenance target))
            (fun row row' : BHist => hsame row row') := by
  intro carrier certBridgeRead bridgePkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_transport certUnary certBridgeRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary, bridgePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      have certRow : hsame cert row :=
        hsame_trans certBridgeRead (hsame_symm sourceRow.left)
      exact
        ⟨cont_result_hsame_transport provenanceTargetCert certRow, sourceGraphLanding,
          landingRoutesTarget⟩
    ledger_sound := by
      intro row sourceRow
      have bridgeCert : hsame bridgeRead cert :=
        hsame_symm certBridgeRead
      have rowEndpoint : hsame row (append provenance target) :=
        hsame_trans sourceRow.left (hsame_trans bridgeCert certMatchesEndpoint)
      exact ⟨sourceRow.right.right, rowEndpoint⟩
  }

theorem CertificateCompilerCarrier_bridge_consumer_exhaustion [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget compositeTarget
      tripleTarget bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame identityTarget source ->
        Cont target graph compositeTarget ->
          Cont compositeTarget routes tripleTarget ->
            hsame cert bridgeRead ->
              PkgSig bundle tripleTarget pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row tripleTarget ∧ UnaryHistory row ∧
                    PkgSig bundle row pkg)
                  (fun row : BHist => Cont compositeTarget routes row ∧
                    Cont target graph compositeTarget ∧ Cont source graph landing ∧
                      Cont landing routes target)
                  (fun row : BHist => PkgSig bundle row pkg ∧
                    hsame bridgeRead (append provenance target))
                  (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier _identitySame targetGraphComposite compositeRoutesTriple certBridgeRead triplePkg
  obtain ⟨_sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have bridgeLedger : hsame bridgeRead (append provenance target) :=
    hsame_trans (hsame_symm certBridgeRead) certMatchesEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro tripleTarget ⟨hsame_refl tripleTarget, tripleUnary, triplePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport compositeRoutesTriple (hsame_symm sourceRow.left),
          targetGraphComposite, sourceGraphLanding, landingRoutesTarget⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, bridgeLedger⟩
  }

theorem CertificateCompilerCarrier_bridge_associativity_split_index [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget compositeTarget
      tripleTarget bridgeRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame identityTarget source ->
        Cont target graph compositeTarget ->
          Cont compositeTarget routes tripleTarget ->
            hsame cert bridgeRead ->
              Cont tripleTarget cert exported ->
                PkgSig bundle exported pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
                      PkgSig bundle row pkg)
                    (fun row : BHist => Cont tripleTarget cert row ∧
                      Cont target graph compositeTarget ∧ Cont compositeTarget routes tripleTarget)
                    (fun row : BHist => PkgSig bundle row pkg ∧
                      hsame bridgeRead (append provenance target) ∧
                        Cont source graph landing ∧ Cont landing routes target)
                    (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier identitySame targetGraphComposite compositeRoutesTriple certBridgeRead
    tripleCertExported exportedPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have _identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed tripleUnary certUnary tripleCertExported
  have bridgeLedger : hsame bridgeRead (append provenance target) :=
    hsame_trans (hsame_symm certBridgeRead) certMatchesEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportedPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport tripleCertExported (hsame_symm sourceRow.left),
          targetGraphComposite, compositeRoutesTriple⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right.right, bridgeLedger, sourceGraphLanding, landingRoutesTarget⟩
  }

theorem CertificateCompilerCarrier_ledger_cut_elimination [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert cutEndpoint cutCert
      retained : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg ->
      hsame cutEndpoint target ->
        hsame cutCert cert ->
          Cont cutEndpoint provenance retained ->
            PkgSig bundle retained pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row retained ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist => Cont cutEndpoint provenance row ∧
                  Cont source graph landing ∧ Cont landing routes target)
                (fun row : BHist => PkgSig bundle row pkg ∧
                  hsame cutCert (append provenance target))
                (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg SemanticNameCert
  intro carrier endpointSame cutCertSame cutRoute retainedPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have cutEndpointUnary : UnaryHistory cutEndpoint :=
    unary_transport targetUnary (hsame_symm endpointSame)
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed cutEndpointUnary provenanceUnary cutRoute
  have cutCertLedger : hsame cutCert (append provenance target) :=
    hsame_trans cutCertSame certMatchesEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro retained ⟨hsame_refl retained, retainedUnary, retainedPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport cutRoute (hsame_symm sourceRow.left),
          sourceGraphLanding, landingRoutesTarget⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, cutCertLedger⟩
  }

end BEDC.Derived.CertificateCompilerUp
