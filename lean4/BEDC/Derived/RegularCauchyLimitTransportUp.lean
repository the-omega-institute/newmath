import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

end BEDC.Derived.RegularCauchyLimitTransportUp
