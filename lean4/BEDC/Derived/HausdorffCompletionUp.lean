import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HausdorffCompletionCarrier [AskSetup] [PackageSetup]
    (source entourage separated handoff transport route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
    UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ Cont source entourage transport ∧
        Cont separated handoff route ∧ Cont transport route provenance ∧
          PkgSig bundle provenance pkg

theorem HausdorffCompletionCarrier_classifier_transport [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance source' entourage'
      separated' handoff' transport' route' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      hsame source source' ->
        hsame entourage entourage' ->
          hsame separated separated' ->
            hsame handoff handoff' ->
              hsame transport transport' ->
                Cont separated' handoff' route' ->
                  Cont transport' route' provenance' ->
                    PkgSig bundle provenance' pkg ->
                      HausdorffCompletionCarrier source' entourage' separated' handoff'
                          transport' route' provenance' bundle pkg ∧
                        hsame route route' := by
  intro carrier sameSource sameEntourage sameSeparated sameHandoff sameTransport routeRow'
    provenanceRow' provenancePkg'
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary, routeUnary,
    provenanceUnary, sourceEntourageRow, routeRow, provenanceRow, _provenancePkg⟩ := carrier
  have transportRow' : Cont source' entourage' transport' :=
    cont_intro
      (sameTransport.symm.trans
        (cont_respects_hsame sameSource sameEntourage sourceEntourageRow (cont_intro rfl)))
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameSeparated sameHandoff routeRow routeRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameRoute provenanceRow provenanceRow'
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have entourageUnary' : UnaryHistory entourage' := unary_transport entourageUnary sameEntourage
  have separatedUnary' : UnaryHistory separated' := unary_transport separatedUnary sameSeparated
  have handoffUnary' : UnaryHistory handoff' := unary_transport handoffUnary sameHandoff
  have transportUnary' : UnaryHistory transport' := unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨sourceUnary', entourageUnary', separatedUnary', handoffUnary', transportUnary',
        routeUnary', provenanceUnary', transportRow', routeRow', provenanceRow',
        provenancePkg'⟩,
      sameRoute⟩

theorem HausdorffCompletionCarrier_uniform_entourage_cauchy_handoff [AskSetup]
    [PackageSetup]
    {source entourage separated handoff transport route provenance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont entourage handoff consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory handoff ∧
            UnaryHistory consumer ∧ Cont source entourage transport ∧
              Cont entourage handoff consumer ∧ Cont transport route provenance ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  intro carrier entourageHandoffConsumer consumerPkg
  obtain ⟨sourceUnary, entourageUnary, _separatedUnary, handoffUnary, _transportUnary,
    _routeUnary, _provenanceUnary, sourceEntourageTransport, _separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed entourageUnary handoffUnary entourageHandoffConsumer
  exact
    ⟨sourceUnary, entourageUnary, handoffUnary, consumerUnary, sourceEntourageTransport,
      entourageHandoffConsumer, transportRouteProvenance, provenancePkg, consumerPkg⟩

theorem HausdorffCompletionCarrier_cauchy_entourage_handoff_exactness [AskSetup]
    [PackageSetup]
    {source entourage separated handoff transport route provenance consumer endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont source entourage consumer ->
        Cont consumer handoff endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory handoff ∧
              UnaryHistory consumer ∧ UnaryHistory endpoint ∧ Cont source entourage transport ∧
                Cont source entourage consumer ∧ hsame transport consumer ∧
                  Cont consumer handoff endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier sourceEntourageConsumer consumerHandoffEndpoint endpointPkg
  obtain ⟨sourceUnary, entourageUnary, _separatedUnary, handoffUnary, transportUnary,
    _routeUnary, _provenanceUnary, sourceEntourageTransport, _separatedHandoffRoute,
    _transportRouteProvenance, provenancePkg⟩ := carrier
  have sameTransportConsumer : hsame transport consumer :=
    cont_deterministic sourceEntourageTransport sourceEntourageConsumer
  have consumerUnary : UnaryHistory consumer :=
    unary_transport transportUnary sameTransportConsumer
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed consumerUnary handoffUnary consumerHandoffEndpoint
  exact
    ⟨sourceUnary, entourageUnary, handoffUnary, consumerUnary, endpointUnary,
      sourceEntourageTransport, sourceEntourageConsumer, sameTransportConsumer,
      consumerHandoffEndpoint, provenancePkg, endpointPkg⟩

theorem HausdorffCompletionCarrier_separated_seal_boundary [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont separated provenance sealConsumer ->
        PkgSig bundle sealConsumer pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
            UnaryHistory provenance ∧ UnaryHistory sealConsumer ∧
              Cont source entourage transport ∧ Cont separated handoff route ∧
                Cont transport route provenance ∧ Cont separated provenance sealConsumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealConsumer pkg := by
  intro carrier separatedProvenanceSealConsumer sealConsumerPkg
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, _handoffUnary, _transportUnary,
    _routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed separatedUnary provenanceUnary separatedProvenanceSealConsumer
  exact
    ⟨sourceUnary, entourageUnary, separatedUnary, provenanceUnary, sealConsumerUnary,
      sourceEntourageTransport, separatedHandoffRoute, transportRouteProvenance,
      separatedProvenanceSealConsumer, provenancePkg, sealConsumerPkg⟩

theorem HausdorffCompletionCarrier_separated_reflector_route [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance publicRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont source handoff publicRoute ->
        PkgSig bundle publicRoute pkg ->
          UnaryHistory source ∧ UnaryHistory handoff ∧ UnaryHistory publicRoute ∧
            Cont source handoff publicRoute ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle publicRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier sourceHandoffPublicRoute publicRoutePkg
  obtain ⟨sourceUnary, _entourageUnary, _separatedUnary, handoffUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _sourceEntourageTransport, _separatedHandoffRoute,
    _transportRouteProvenance, provenancePkg⟩ := carrier
  have publicRouteUnary : UnaryHistory publicRoute :=
    unary_cont_closed sourceUnary handoffUnary sourceHandoffPublicRoute
  exact
    ⟨sourceUnary, handoffUnary, publicRouteUnary, sourceHandoffPublicRoute, provenancePkg,
      publicRoutePkg⟩

theorem HausdorffCompletionCarrier_real_seal_ledger_scope [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont separated provenance sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist =>
              Cont separated provenance row ∧
                HausdorffCompletionCarrier source entourage separated handoff transport route
                  provenance bundle pkg)
            (fun _row : BHist => PkgSig bundle sealRead pkg ∧
              Cont separated provenance sealRead)
            (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier separatedProvenanceSealRead sealReadPkg
  have acceptedCarrier :
      HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg := carrier
  obtain ⟨_sourceUnary, _entourageUnary, separatedUnary, _handoffUnary, _transportUnary,
    _routeUnary, provenanceUnary, _sourceEntourageTransport, _separatedHandoffRoute,
    _transportRouteProvenance, _provenancePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedUnary provenanceUnary separatedProvenanceSealRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary, sealReadPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport separatedProvenanceSealRead
            (hsame_symm sourceRow.left),
          acceptedCarrier⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨sealReadPkg, separatedProvenanceSealRead⟩
  }

theorem HausdorffCompletionCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont provenance route ledger ->
        PkgSig bundle ledger pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
            UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory ledger ∧
                Cont source entourage transport ∧ Cont separated handoff route ∧
                  Cont transport route provenance ∧ Cont provenance route ledger ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledger pkg := by
  intro carrier provenanceRouteLedger ledgerPkg
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
    routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary routeUnary provenanceRouteLedger
  exact
    ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary, routeUnary,
      provenanceUnary, ledgerUnary, sourceEntourageTransport, separatedHandoffRoute,
      transportRouteProvenance, provenanceRouteLedger, provenancePkg, ledgerPkg⟩

theorem HausdorffCompletionCarrier_public_certificate [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HausdorffCompletionCarrier source entourage separated handoff transport route
            provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          Cont transport route row ∧
            HausdorffCompletionCarrier source entourage separated handoff transport route
              provenance bundle pkg)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont transport route provenance)
        (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg NameCert hsame Cont
  intro accepted
  have acceptedCarrier :
      HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg := accepted
  obtain ⟨_sourceUnary, _entourageUnary, _separatedUnary, _handoffUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _sourceEntourageTransport,
    _separatedHandoffRoute, transportRouteProvenance, provenancePkg⟩ := accepted
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨acceptedCarrier, hsame_refl provenance⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport transportRouteProvenance (hsame_symm source.right),
          source.left⟩
    ledger_sound := by
      intro _row source
      cases source.right
      exact ⟨provenancePkg, transportRouteProvenance⟩
  }

def HausdorffCompletionPacket [AskSetup] [PackageSetup]
    (source entourage sealRow handoff transports routes provenance nameRow exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory handoff ∧
    UnaryHistory routes ∧ UnaryHistory nameRow ∧ Cont source entourage sealRow ∧
      Cont sealRow handoff transports ∧ Cont transports routes provenance ∧
        Cont provenance nameRow exported ∧ PkgSig bundle exported pkg

theorem HausdorffCompletionPacket_namecert_obligations [AskSetup] [PackageSetup]
    {source entourage sealRow handoff transports routes provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionPacket source entourage sealRow handoff transports routes provenance
        nameRow exported bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont provenance nameRow row ∧
          Cont source entourage sealRow ∧ Cont sealRow handoff transports)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont transports routes provenance ∧
          Cont provenance nameRow exported)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨sourceUnary, entourageUnary, handoffUnary, routesUnary, nameRowUnary,
    sourceEntourageSeal, sealHandoffTransports, transportsRoutesProvenance,
    provenanceNameExported, exportedPkg⟩ := packet
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed sourceUnary entourageUnary sourceEntourageSeal
  have transportsUnary : UnaryHistory transports :=
    unary_cont_closed sealRowUnary handoffUnary sealHandoffTransports
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportsUnary routesUnary transportsRoutesProvenance
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed provenanceUnary nameRowUnary provenanceNameExported
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportedPkg⟩
      equiv_refl := by
        intro row _source
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
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport provenanceNameExported (hsame_symm sourceRow.left),
          sourceEntourageSeal, sealHandoffTransports⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, transportsRoutesProvenance, provenanceNameExported⟩
  }

end BEDC.Derived.HausdorffCompletionUp
