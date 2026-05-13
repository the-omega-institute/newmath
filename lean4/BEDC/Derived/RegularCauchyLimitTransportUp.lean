import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.RealCompletenessUp

namespace BEDC.Derived.RegularCauchyLimitTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealCompletenessUp

def RegularCauchyLimitTransportCarrier [AskSetup] [PackageSetup]
    (sourceRow windowRow dyadicRow sealRow transportRow routeRow provenanceRow localCertRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceRow ∧ UnaryHistory windowRow ∧ UnaryHistory dyadicRow ∧
    UnaryHistory sealRow ∧ UnaryHistory transportRow ∧ UnaryHistory routeRow ∧
      UnaryHistory provenanceRow ∧ UnaryHistory localCertRow ∧
        Cont sourceRow windowRow dyadicRow ∧ Cont dyadicRow sealRow routeRow ∧
          Cont routeRow transportRow provenanceRow ∧ Cont provenanceRow sealRow localCertRow ∧
            hsame transportRow (append sourceRow sealRow) ∧ PkgSig bundle provenanceRow pkg ∧
              PkgSig bundle localCertRow pkg

def RegularCauchyLimitTransportClassifier
    (source window dyadic sealRow transport routes provenance cert
      source' window' dyadic' sealRow' transport' routes' provenance' cert' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame source source' ∧ hsame window window' ∧ hsame dyadic dyadic' ∧
    hsame sealRow sealRow' ∧ hsame transport transport' ∧ hsame routes routes' ∧
      hsame provenance provenance' ∧ hsame cert cert'

theorem RegularCauchyLimitTransportCarrier_stability [AskSetup] [PackageSetup]
    {sourceRow windowRow dyadicRow sealRow transportRow routeRow provenanceRow localCertRow
      sourceRow' windowRow' dyadicRow' sealRow' routeRow' provenanceRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier sourceRow windowRow dyadicRow sealRow transportRow
        routeRow provenanceRow localCertRow bundle pkg ->
      hsame sourceRow sourceRow' ->
        hsame windowRow windowRow' ->
          hsame sealRow sealRow' ->
            Cont sourceRow' windowRow' dyadicRow' ->
              Cont dyadicRow' sealRow' routeRow' ->
                Cont routeRow' transportRow provenanceRow' ->
                  PkgSig bundle provenanceRow' pkg ->
                    RegularCauchyLimitTransportCarrier sourceRow' windowRow' dyadicRow'
                      sealRow' transportRow routeRow' provenanceRow' localCertRow bundle pkg ∧
                    hsame dyadicRow dyadicRow' ∧ hsame routeRow routeRow' ∧
                      hsame provenanceRow provenanceRow' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier sameSource sameWindow sameSeal sourceWindowDyadic' dyadicSealRoute'
    routeTransportProvenance' provenancePkg'
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, transportUnary, routeUnary,
    provenanceUnary, localCertUnary, sourceWindowDyadic, dyadicSealRoute,
    routeTransportProvenance, provenanceSealLocalCert, transportMatchesSeal,
    _provenancePkg, localCertPkg⟩ := carrier
  have sameDyadic : hsame dyadicRow dyadicRow' :=
    cont_respects_hsame sameSource sameWindow sourceWindowDyadic sourceWindowDyadic'
  have sameRoute : hsame routeRow routeRow' :=
    cont_respects_hsame sameDyadic sameSeal dyadicSealRoute dyadicSealRoute'
  have sameProvenance : hsame provenanceRow provenanceRow' :=
    cont_respects_hsame sameRoute (hsame_refl transportRow) routeTransportProvenance
      routeTransportProvenance'
  have provenanceSealLocalCert' : Cont provenanceRow' sealRow' localCertRow := by
    cases sameProvenance
    cases sameSeal
    exact provenanceSealLocalCert
  have transportMatchesSeal' : hsame transportRow (append sourceRow' sealRow') := by
    cases sameSource
    cases sameSeal
    exact transportMatchesSeal
  have transported :
      RegularCauchyLimitTransportCarrier sourceRow' windowRow' dyadicRow' sealRow'
        transportRow routeRow' provenanceRow' localCertRow bundle pkg := by
    exact
      ⟨unary_transport sourceUnary sameSource, unary_transport windowUnary sameWindow,
        unary_transport dyadicUnary sameDyadic, unary_transport sealUnary sameSeal,
        transportUnary, unary_transport routeUnary sameRoute,
        unary_transport provenanceUnary sameProvenance, localCertUnary, sourceWindowDyadic',
        dyadicSealRoute', routeTransportProvenance', provenanceSealLocalCert',
        transportMatchesSeal', provenancePkg', localCertPkg⟩
  exact ⟨transported, sameDyadic, sameRoute, sameProvenance⟩

theorem RegularCauchyLimitTransportCarrier_dyadic_ledger_stability [AskSetup]
    [PackageSetup]
    {sourceRow windowRow dyadicRow sealRow transportRow routeRow provenanceRow localCertRow
      sourceRow' windowRow' dyadicRow' sealRow' routeRow' provenanceRow' handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier sourceRow windowRow dyadicRow sealRow transportRow
        routeRow provenanceRow localCertRow bundle pkg ->
      hsame sourceRow sourceRow' ->
        hsame windowRow windowRow' ->
          hsame sealRow sealRow' ->
            Cont sourceRow' windowRow' dyadicRow' ->
              Cont dyadicRow' sealRow' routeRow' ->
                Cont routeRow' transportRow provenanceRow' ->
                  PkgSig bundle provenanceRow' pkg ->
                    Cont routeRow' localCertRow handoff ->
                      RegularCauchyLimitTransportCarrier sourceRow' windowRow' dyadicRow'
                          sealRow' transportRow routeRow' provenanceRow' localCertRow bundle pkg ∧
                        hsame dyadicRow dyadicRow' ∧ UnaryHistory dyadicRow' ∧
                          UnaryHistory handoff ∧ Cont sourceRow' windowRow' dyadicRow' ∧
                            Cont dyadicRow' sealRow' routeRow' ∧
                              Cont routeRow' localCertRow handoff ∧
                                PkgSig bundle provenanceRow' pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier sameSource sameWindow sameSeal sourceWindowDyadic' dyadicSealRoute'
    routeTransportProvenance' provenancePkg' routeLocalCertHandoff
  obtain ⟨transported, sameDyadic, _sameRoute, _sameProvenance⟩ :=
    RegularCauchyLimitTransportCarrier_stability carrier sameSource sameWindow sameSeal
      sourceWindowDyadic' dyadicSealRoute' routeTransportProvenance' provenancePkg'
  have transportedRows := transported
  obtain ⟨_sourceUnary, _windowUnary, dyadicUnary', _sealUnary, _transportUnary, routeUnary',
    _provenanceUnary, localCertUnary, _sourceWindowDyadic, _dyadicSealRoute,
    _routeTransportProvenance, _provenanceSealLocalCert, _transportMatchesSeal,
    _provenancePkg, _localCertPkg⟩ := transportedRows
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary' localCertUnary routeLocalCertHandoff
  exact
    ⟨transported, sameDyadic, dyadicUnary', handoffUnary, sourceWindowDyadic',
      dyadicSealRoute', routeLocalCertHandoff, provenancePkg'⟩

theorem RegularCauchyLimitTransportCarrier_namecert_obligations [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance cert
        bundle pkg ->
      UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
        UnaryHistory sealRow ∧ UnaryHistory routes ∧ Cont source window dyadic ∧
          Cont dyadic sealRow routes ∧ hsame transport (append source sealRow) ∧
            PkgSig bundle cert pkg := by
  intro carrier
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _certUnary, sourceWindowDyadic, dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, transportMatchesSeal,
    _provenancePkg, certPkg⟩ := carrier
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed dyadicUnary sealUnary dyadicSealRoutes
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, routesUnary, sourceWindowDyadic,
      dyadicSealRoutes, transportMatchesSeal, certPkg⟩

theorem RegularCauchyLimitTransportCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance
        cert bundle pkg ->
      Cont routes cert handoff ->
        UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
          UnaryHistory sealRow ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
            UnaryHistory cert ∧ UnaryHistory handoff ∧ Cont source window dyadic ∧
              Cont dyadic sealRow routes ∧ Cont routes cert handoff ∧
                hsame transport (append source sealRow) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier routesCertHandoff
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, _transportUnary, routesUnary,
    provenanceUnary, certUnary, sourceWindowDyadic, dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, transportMatchesSeal,
    provenancePkg, certPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routesUnary certUnary routesCertHandoff
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, routesUnary, provenanceUnary,
      certUnary, handoffUnary, sourceWindowDyadic, dyadicSealRoutes, routesCertHandoff,
      transportMatchesSeal, provenancePkg, certPkg⟩

theorem RegularCauchyLimitTransportCarrier_classifier_handoff_coverage [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert source' window' dyadic'
      sealRow' transport' routes' provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance
        cert bundle pkg ->
      RegularCauchyLimitTransportCarrier source' window' dyadic' sealRow' transport' routes'
        provenance' cert' bundle pkg ->
        hsame source source' ->
          hsame window window' ->
            hsame sealRow sealRow' ->
              hsame transport transport' ->
                RegularCauchyLimitTransportClassifier source window dyadic sealRow transport routes
                    provenance cert source' window' dyadic' sealRow' transport' routes'
                    provenance' cert' ∧
                  hsame dyadic dyadic' ∧ hsame routes routes' ∧
                    hsame provenance provenance' ∧ hsame cert cert' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier carrier' sameSource sameWindow sameSeal sameTransport
  obtain ⟨_sourceUnary, _windowUnary, _dyadicUnary, _sealUnary, _transportUnary,
    _routesUnary, _provenanceUnary, _certUnary, sourceWindowDyadic, dyadicSealRoutes,
    routesTransportProvenance, provenanceSealCert, _transportMatchesSeal, _provenancePkg,
    _certPkg⟩ := carrier
  obtain ⟨_sourceUnary', _windowUnary', _dyadicUnary', _sealUnary', _transportUnary',
    _routesUnary', _provenanceUnary', _certUnary', sourceWindowDyadic',
    dyadicSealRoutes', routesTransportProvenance', provenanceSealCert',
    _transportMatchesSeal', _provenancePkg', _certPkg'⟩ := carrier'
  have sameDyadic : hsame dyadic dyadic' :=
    cont_respects_hsame sameSource sameWindow sourceWindowDyadic sourceWindowDyadic'
  have sameRoutes : hsame routes routes' :=
    cont_respects_hsame sameDyadic sameSeal dyadicSealRoutes dyadicSealRoutes'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRoutes sameTransport routesTransportProvenance
      routesTransportProvenance'
  have sameCert : hsame cert cert' :=
    cont_respects_hsame sameProvenance sameSeal provenanceSealCert provenanceSealCert'
  have classifier :
      RegularCauchyLimitTransportClassifier source window dyadic sealRow transport routes
        provenance cert source' window' dyadic' sealRow' transport' routes' provenance'
        cert' := by
    exact
      ⟨sameSource, sameWindow, sameDyadic, sameSeal, sameTransport, sameRoutes,
        sameProvenance, sameCert⟩
  exact ⟨classifier, sameDyadic, sameRoutes, sameProvenance, sameCert⟩

theorem RegularCauchyLimitTransportCarrier_completion_boundary_nonescape [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert handoff boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance
        cert bundle pkg ->
      Cont routes cert handoff ->
        Cont handoff sealRow boundary ->
          UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory sealRow ∧ UnaryHistory routes ∧ UnaryHistory handoff ∧
              UnaryHistory boundary ∧ Cont source window dyadic ∧
                Cont dyadic sealRow routes ∧ Cont routes cert handoff ∧
                  Cont handoff sealRow boundary ∧ hsame transport (append source sealRow) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier routesCertHandoff handoffSealBoundary
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, _transportUnary, routesUnary,
    _provenanceUnary, certUnary, sourceWindowDyadic, dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, transportMatchesSeal,
    provenancePkg, certPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routesUnary certUnary routesCertHandoff
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed handoffUnary sealUnary handoffSealBoundary
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, routesUnary, handoffUnary,
      boundaryUnary, sourceWindowDyadic, dyadicSealRoutes, routesCertHandoff,
      handoffSealBoundary, transportMatchesSeal, provenancePkg, certPkg⟩

theorem RegularCauchyLimitTransportCarrier_real_completeness_consumer_factorization
    [AskSetup] [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert family modulus readback endpoint
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance
        cert bundle pkg ->
      RealCompletenessBHistCarrier family modulus source dyadic window readback sealRow transport
        routes provenance cert endpoint bundle pkg ->
        Cont sealRow cert publicRead ->
          UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory sealRow ∧ UnaryHistory publicRead ∧ Cont source window dyadic ∧
              Cont dyadic sealRow routes ∧ Cont sealRow cert publicRead ∧
                PkgSig bundle cert pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory RealCompletenessBHistCarrier
  intro transportCarrier realCarrier sealCertPublicRead
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _certUnary, sourceWindowDyadic, dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, _transportMatchesSeal,
    _provenancePkg, certPkg⟩ := transportCarrier
  obtain ⟨_familyUnary, _modulusUnary, _sourceUnaryReal, _dyadicUnaryReal, _windowUnaryReal,
    _readbackUnary, _sealUnaryReal, _transportUnaryReal, _routesUnaryReal,
    _provenanceUnaryReal, certUnaryReal, _endpointUnary, _transportRouteEndpoint,
    endpointPkg⟩ := realCarrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary certUnaryReal sealCertPublicRead
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, sealUnary, publicReadUnary, sourceWindowDyadic,
      dyadicSealRoutes, sealCertPublicRead, certPkg, endpointPkg⟩

theorem RegularCauchyLimitTransportCarrier_selected_window_exactness [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert observed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance
        cert bundle pkg ->
      Cont source window observed ->
        UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory observed ∧
          hsame dyadic observed ∧ Cont source window observed ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectedWindowRoute
  obtain ⟨sourceUnary, windowUnary, _dyadicUnary, _sealUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _certUnary, storedWindowRoute, _dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, _transportMatchesSeal, provenancePkg,
    certPkg⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed sourceUnary windowUnary selectedWindowRoute
  have dyadicObserved : hsame dyadic observed :=
    cont_respects_hsame (hsame_refl source) (hsame_refl window) storedWindowRoute
      selectedWindowRoute
  exact
    ⟨sourceUnary, windowUnary, observedUnary, dyadicObserved, selectedWindowRoute,
      provenancePkg, certPkg⟩

theorem RegularCauchyLimitTransportCarrier_window_dyadic_seal_triangle [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert observed sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes provenance
        cert bundle pkg ->
      Cont source window observed ->
        Cont observed sealRow sealRead ->
          UnaryHistory observed ∧ UnaryHistory sealRead ∧ hsame dyadic observed ∧
            hsame routes sealRead ∧ Cont source window observed ∧
              Cont observed sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectedWindowRoute observedSealRead
  obtain ⟨sourceUnary, windowUnary, _dyadicUnary, sealUnary, _transportUnary,
    _routesUnary, _provenanceUnary, _certUnary, storedWindowRoute, dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, _transportMatchesSeal, provenancePkg,
    certPkg⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed sourceUnary windowUnary selectedWindowRoute
  have dyadicObserved : hsame dyadic observed :=
    cont_respects_hsame (hsame_refl source) (hsame_refl window) storedWindowRoute
      selectedWindowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed observedUnary sealUnary observedSealRead
  have routesSealRead : hsame routes sealRead :=
    cont_respects_hsame dyadicObserved (hsame_refl sealRow) dyadicSealRoutes observedSealRead
  exact
    ⟨observedUnary, sealReadUnary, dyadicObserved, routesSealRead, selectedWindowRoute,
      observedSealRead, provenancePkg, certPkg⟩

theorem RegularCauchyLimitTransportCarrier_seal_route_determinacy [AskSetup]
    [PackageSetup]
    {source window dyadic sealRow transport routes provenance cert observed sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitTransportCarrier source window dyadic sealRow transport routes
        provenance cert bundle pkg →
      Cont source window observed →
        Cont observed sealRow sealRead →
          Cont sealRead cert publicRead →
            UnaryHistory observed ∧ UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
              hsame dyadic observed ∧ hsame routes sealRead ∧
                Cont source window observed ∧ Cont observed sealRow sealRead ∧
                  Cont sealRead cert publicRead ∧ hsame transport (append source sealRow) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectedWindowRoute observedSealRead sealReadCertPublicRead
  obtain ⟨sourceUnary, windowUnary, _dyadicUnary, sealUnary, _transportUnary,
    _routesUnary, _provenanceUnary, certUnary, storedWindowRoute, dyadicSealRoutes,
    _routesTransportProvenance, _provenanceSealCert, transportMatchesSeal, provenancePkg,
    certPkg⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed sourceUnary windowUnary selectedWindowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed observedUnary sealUnary observedSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary certUnary sealReadCertPublicRead
  have dyadicObserved : hsame dyadic observed :=
    cont_respects_hsame (hsame_refl source) (hsame_refl window) storedWindowRoute
      selectedWindowRoute
  have routesSealRead : hsame routes sealRead :=
    cont_respects_hsame dyadicObserved (hsame_refl sealRow) dyadicSealRoutes observedSealRead
  exact
    ⟨observedUnary, sealReadUnary, publicReadUnary, dyadicObserved, routesSealRead,
      selectedWindowRoute, observedSealRead, sealReadCertPublicRead, transportMatchesSeal,
      provenancePkg, certPkg⟩

end BEDC.Derived.RegularCauchyLimitTransportUp
