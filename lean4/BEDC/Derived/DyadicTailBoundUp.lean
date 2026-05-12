import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicTailBoundCarrier [AskSetup] [PackageSetup]
    (precision schedule tolerance ledger readback «seal» transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
    UnaryHistory readback ∧ UnaryHistory «seal» ∧ UnaryHistory provenance ∧
      Cont schedule tolerance ledger ∧ Cont ledger readback «seal» ∧
        Cont precision «seal» transport ∧ Cont transport localCert route ∧
          Cont route provenance «seal» ∧ PkgSig bundle provenance pkg

theorem DyadicTailBoundCarrier_regseqrat_handoff_exactness [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback «seal» transport route provenance localCert
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback «seal» transport route
        provenance localCert bundle pkg ->
      Cont ledger readback consumerRead ->
        UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory consumerRead ∧
            Cont schedule tolerance ledger ∧ Cont ledger readback consumerRead ∧
              PkgSig bundle provenance pkg := by
  intro carrier consumerRow
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    _provenanceUnary, scheduleToleranceRow, _sealRow, _transportRow, _routeRow,
    _sealRouteRow, pkgSig⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary readbackUnary consumerRow
  exact ⟨precisionUnary, scheduleUnary, toleranceUnary, ledgerUnary, readbackUnary,
    consumerUnary, scheduleToleranceRow, consumerRow, pkgSig⟩

theorem DyadicTailBoundCarrier_classifier_transport_exactness [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      precision' schedule' tolerance' ledger' readback' sealRow' transport' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      hsame precision precision' -> hsame schedule schedule' -> hsame tolerance tolerance' ->
        hsame readback readback' -> Cont schedule' tolerance' ledger' ->
          Cont ledger' readback' sealRow' -> Cont precision' sealRow' transport' ->
            Cont transport' localCert route' -> Cont route' provenance sealRow' ->
              PkgSig bundle provenance pkg ->
                DyadicTailBoundCarrier precision' schedule' tolerance' ledger' readback' sealRow'
                    transport' route' provenance localCert bundle pkg ∧
                  hsame ledger ledger' ∧ hsame sealRow sealRow' ∧ hsame transport transport' ∧
                    hsame route route' := by
  intro carrier samePrecision sameSchedule sameTolerance sameReadback ledgerCont' sealCont'
    transportCont' routeCont' sealRouteCont' pkgSig'
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    provenanceUnary, ledgerCont, sealCont, transportCont, routeCont, _sealRouteCont,
    _pkgSig⟩ := carrier
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed scheduleUnary' toleranceUnary' ledgerCont'
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed ledgerUnary' readbackUnary' sealCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSchedule sameTolerance ledgerCont ledgerCont'
  have sameSeal : hsame sealRow sealRow' :=
    cont_respects_hsame sameLedger sameReadback sealCont sealCont'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameSeal transportCont transportCont'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameTransport (hsame_refl localCert) routeCont routeCont'
  have transported :
      DyadicTailBoundCarrier precision' schedule' tolerance' ledger' readback' sealRow'
          transport' route' provenance localCert bundle pkg :=
    ⟨unary_transport precisionUnary samePrecision,
      scheduleUnary',
      toleranceUnary',
      readbackUnary',
      sealUnary',
      provenanceUnary,
      ledgerCont',
      sealCont',
      transportCont',
      routeCont',
      sealRouteCont',
      pkgSig'⟩
  exact
    ⟨transported,
      sameLedger,
      sameSeal,
      sameTransport,
      sameRoute⟩

theorem DyadicTailBoundCarrier_precision_refinement_stability [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      precision' sealRow' transport' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      hsame precision precision' ->
        Cont ledger readback sealRow' ->
          Cont precision' sealRow' transport' ->
            Cont transport' localCert route' ->
              Cont route' provenance sealRow' ->
                PkgSig bundle provenance pkg ->
                  DyadicTailBoundCarrier precision' schedule tolerance ledger readback sealRow'
                    transport' route' provenance localCert bundle pkg ∧
                    hsame sealRow sealRow' ∧ hsame transport transport' ∧
                      hsame route route' := by
  intro carrier samePrecision sealCont' transportCont' routeCont' sealRouteCont' pkgSig'
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    provenanceUnary, ledgerCont, sealCont, transportCont, routeCont, _sealRouteCont,
    _pkgSig⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary ledgerCont
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed ledgerUnary readbackUnary sealCont'
  have sameSeal : hsame sealRow sealRow' :=
    cont_respects_hsame (hsame_refl ledger) (hsame_refl readback) sealCont sealCont'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameSeal transportCont transportCont'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameTransport (hsame_refl localCert) routeCont routeCont'
  have rebuilt :
      DyadicTailBoundCarrier precision' schedule tolerance ledger readback sealRow'
          transport' route' provenance localCert bundle pkg :=
    ⟨unary_transport precisionUnary samePrecision,
      scheduleUnary,
      toleranceUnary,
      readbackUnary,
      sealUnary',
      provenanceUnary,
      ledgerCont,
      sealCont',
      transportCont',
      routeCont',
      sealRouteCont',
      pkgSig'⟩
  exact ⟨rebuilt, sameSeal, sameTransport, sameRoute⟩

theorem DyadicTailBoundCarrier_precision_window_restriction [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
        UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
          UnaryHistory provenance ∧ Cont schedule tolerance ledger ∧
            Cont ledger readback sealRow ∧ Cont precision sealRow transport ∧
              Cont transport localCert route ∧ Cont route provenance sealRow ∧
                PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, sealRowUnary,
    provenanceUnary, scheduleToleranceLedger, ledgerReadbackSeal, precisionSealTransport,
    transportLocalRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  exact
    ⟨precisionUnary,
      scheduleUnary,
      toleranceUnary,
      ledgerUnary,
      readbackUnary,
      sealRowUnary,
      provenanceUnary,
      scheduleToleranceLedger,
      ledgerReadbackSeal,
      precisionSealTransport,
      transportLocalRoute,
        routeProvenanceSeal,
        provenancePkg⟩

theorem DyadicTailBoundCarrier_budget_composition [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      ledger2 readback2 sealRow2 compositeLedger compositeReadback compositeSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont schedule tolerance ledger2 ->
        Cont ledger ledger2 compositeLedger ->
          Cont schedule tolerance compositeLedger ->
            UnaryHistory readback2 ->
              Cont compositeLedger readback2 compositeReadback ->
                UnaryHistory sealRow2 ->
                  Cont compositeReadback sealRow2 compositeSeal ->
                    Cont compositeLedger compositeReadback compositeSeal ->
                      Cont precision compositeSeal transport ->
                        Cont route provenance compositeSeal ->
                          PkgSig bundle compositeSeal pkg ->
                            DyadicTailBoundCarrier precision schedule tolerance compositeLedger
                                compositeReadback compositeSeal transport route provenance localCert
                                bundle pkg ∧
                              UnaryHistory ledger2 ∧ UnaryHistory compositeLedger ∧
                                UnaryHistory compositeReadback ∧ UnaryHistory compositeSeal ∧
                                  PkgSig bundle compositeSeal pkg := by
  intro carrier ledger2Cont compositeLedgerCont compositeLedgerScheduleCont readback2Unary
    compositeReadbackCont sealRow2Unary compositeSealCont compositeCarrierSealCont transportCont
    compositeRouteCont compositePkgSig
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, _readbackUnary, _sealUnary,
    provenanceUnary, _ledgerCont, _sealCont, _transportCont, routeCont, _sealRouteCont,
    pkgSig⟩ := carrier
  have ledger2Unary : UnaryHistory ledger2 :=
    unary_cont_closed scheduleUnary toleranceUnary ledger2Cont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary _ledgerCont
  have compositeLedgerUnary : UnaryHistory compositeLedger :=
    unary_cont_closed ledgerUnary ledger2Unary compositeLedgerCont
  have compositeReadbackUnary : UnaryHistory compositeReadback :=
    unary_cont_closed compositeLedgerUnary readback2Unary compositeReadbackCont
  have compositeSealUnary : UnaryHistory compositeSeal :=
    unary_cont_closed compositeReadbackUnary sealRow2Unary compositeSealCont
  have rebuilt :
      DyadicTailBoundCarrier precision schedule tolerance compositeLedger compositeReadback
          compositeSeal transport route provenance localCert bundle pkg :=
    ⟨precisionUnary,
      scheduleUnary,
      toleranceUnary,
      compositeReadbackUnary,
      compositeSealUnary,
      provenanceUnary,
      compositeLedgerScheduleCont,
      compositeCarrierSealCont,
      transportCont,
      routeCont,
      compositeRouteCont,
      pkgSig⟩
  exact
    ⟨rebuilt,
      ledger2Unary,
      compositeLedgerUnary,
      compositeReadbackUnary,
      compositeSealUnary,
      compositePkgSig⟩

theorem DyadicTailBoundCarrier_seal_consumer_determinacy [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      consumer consumer' transport' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont ledger readback consumer ->
        Cont ledger readback consumer' ->
          Cont precision consumer transport ->
            Cont precision consumer' transport' ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle consumer' pkg ->
                  hsame sealRow consumer ∧ hsame sealRow consumer' ∧
                    hsame consumer consumer' ∧ UnaryHistory consumer ∧
                      UnaryHistory consumer' ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumer pkg ∧ PkgSig bundle consumer' pkg := by
  intro carrier consumerRead consumerRead' _consumerTransport _consumerTransport'
    consumerPkg consumerPkg'
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    _provenanceUnary, scheduleToleranceRow, sealRead, _transportRow, _routeRow,
    _sealRouteRow, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceRow
  have sameSealConsumer : hsame sealRow consumer :=
    cont_deterministic sealRead consumerRead
  have sameSealConsumer' : hsame sealRow consumer' :=
    cont_deterministic sealRead consumerRead'
  have sameConsumer : hsame consumer consumer' :=
    hsame_trans (hsame_symm sameSealConsumer) sameSealConsumer'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary readbackUnary consumerRead
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed ledgerUnary readbackUnary consumerRead'
  exact
    ⟨sameSealConsumer, sameSealConsumer', sameConsumer, consumerUnary, consumerUnary',
      provenancePkg, consumerPkg, consumerPkg'⟩

theorem DyadicTailBoundCarrier_consumer_obligation_package [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      consumerRead packageSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont ledger readback consumerRead ->
        Cont consumerRead provenance packageSurface ->
          PkgSig bundle consumerRead pkg ->
            PkgSig bundle packageSurface pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row packageSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist => Cont consumerRead provenance row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow
                      transport route provenance localCert bundle pkg ∧
                    UnaryHistory ledger ∧ UnaryHistory consumerRead ∧ UnaryHistory row)
                hsame := by
  intro carrier ledgerReadbackConsumer consumerProvenancePackage _consumerPkg packagePkg
  have carrierData :
      DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
          provenance localCert bundle pkg :=
    carrier
  have handoff :
      UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
        UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory consumerRead ∧
          Cont schedule tolerance ledger ∧ Cont ledger readback consumerRead ∧
            PkgSig bundle provenance pkg :=
    DyadicTailBoundCarrier_regseqrat_handoff_exactness carrier ledgerReadbackConsumer
  obtain ⟨_precisionUnary, _scheduleUnary, _toleranceUnary, _readbackUnary, _sealUnary,
    provenanceUnary, _scheduleToleranceLedger, _ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have packageUnary : UnaryHistory packageSurface :=
    unary_cont_closed handoff.right.right.right.right.right.left
      provenanceUnary consumerProvenancePackage
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro packageSurface ⟨hsame_refl packageSurface, packageUnary, packagePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨consumerProvenancePackage, packagePkg⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨carrierData, handoff.right.right.right.left,
          handoff.right.right.right.right.right.left, sourceRow.right.left⟩
  }

theorem DyadicTailBoundCarrier_real_seal_factorization [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont ledger readback consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
            UnaryHistory consumer ∧ Cont schedule tolerance ledger ∧
              Cont ledger readback sealRow ∧ Cont ledger readback consumer ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  intro carrier ledgerReadbackConsumer consumerPkg
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, sealRowUnary,
    _provenanceUnary, scheduleToleranceLedger, ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary readbackUnary ledgerReadbackConsumer
  exact
    ⟨ledgerUnary, readbackUnary, sealRowUnary, consumerUnary, scheduleToleranceLedger,
      ledgerReadbackSeal, ledgerReadbackConsumer, provenancePkg, consumerPkg⟩

theorem DyadicTailBoundCarrier_tolerance_ledger_exhaustion [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      PkgSig bundle ledger pkg ->
        UnaryHistory schedule ∧ UnaryHistory tolerance ∧ UnaryHistory ledger ∧
          Cont schedule tolerance ledger ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle ledger pkg := by
  intro carrier ledgerPkg
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _provenanceUnary, scheduleToleranceLedger, _ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  exact
    ⟨scheduleUnary, toleranceUnary, ledgerUnary, scheduleToleranceLedger, provenancePkg,
      ledgerPkg⟩

theorem DyadicTailBoundCarrier_ledger_threshold_exhaustion [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont ledger tolerance comparison ->
        PkgSig bundle comparison pkg ->
          UnaryHistory schedule ∧ UnaryHistory tolerance ∧ UnaryHistory ledger ∧
            UnaryHistory comparison ∧ Cont schedule tolerance ledger ∧
              Cont ledger tolerance comparison ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle comparison pkg := by
  intro carrier ledgerThresholdComparison comparisonPkg
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _provenanceUnary, scheduleToleranceLedger, _ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed ledgerUnary toleranceUnary ledgerThresholdComparison
  exact
    ⟨scheduleUnary, toleranceUnary, ledgerUnary, comparisonUnary, scheduleToleranceLedger,
      ledgerThresholdComparison, provenancePkg, comparisonPkg⟩

theorem DyadicTailBoundCarrier_ledger_comparison_determinacy [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      comparison comparison' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont ledger tolerance comparison ->
        Cont ledger tolerance comparison' ->
          PkgSig bundle comparison pkg ->
            PkgSig bundle comparison' pkg ->
              hsame comparison comparison' ∧ UnaryHistory comparison ∧
                UnaryHistory comparison' ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle comparison pkg ∧ PkgSig bundle comparison' pkg := by
  intro carrier comparisonRow comparisonRow' comparisonPkg comparisonPkg'
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _provenanceUnary, scheduleToleranceLedger, _ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  have sameComparison : hsame comparison comparison' :=
    cont_deterministic comparisonRow comparisonRow'
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed ledgerUnary toleranceUnary comparisonRow
  have comparisonUnary' : UnaryHistory comparison' :=
    unary_cont_closed ledgerUnary toleranceUnary comparisonRow'
  exact
    ⟨sameComparison, comparisonUnary, comparisonUnary', provenancePkg, comparisonPkg,
      comparisonPkg'⟩

theorem DyadicTailBoundCarrier_ledger_append_stability [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      enlargedLedger enlargedSeal transport' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont schedule tolerance enlargedLedger ->
        Cont enlargedLedger readback enlargedSeal ->
          Cont precision enlargedSeal transport' ->
            Cont transport' localCert route' ->
              Cont route' provenance enlargedSeal ->
                PkgSig bundle provenance pkg ->
                  DyadicTailBoundCarrier precision schedule tolerance enlargedLedger readback
                      enlargedSeal transport' route' provenance localCert bundle pkg ∧
                    UnaryHistory enlargedLedger ∧ UnaryHistory enlargedSeal ∧
                      hsame enlargedLedger (append schedule tolerance) ∧
                        hsame enlargedSeal (append enlargedLedger readback) := by
  intro carrier enlargedLedgerCont enlargedSealCont transportCont' routeCont'
    sealRouteCont' pkgSig'
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    provenanceUnary, _ledgerCont, _sealCont, _transportCont, _routeCont, _sealRouteCont,
    _pkgSig⟩ := carrier
  have enlargedLedgerUnary : UnaryHistory enlargedLedger :=
    unary_cont_closed scheduleUnary toleranceUnary enlargedLedgerCont
  have enlargedSealUnary : UnaryHistory enlargedSeal :=
    unary_cont_closed enlargedLedgerUnary readbackUnary enlargedSealCont
  have rebuilt :
      DyadicTailBoundCarrier precision schedule tolerance enlargedLedger readback enlargedSeal
          transport' route' provenance localCert bundle pkg :=
    ⟨precisionUnary,
      scheduleUnary,
      toleranceUnary,
      readbackUnary,
      enlargedSealUnary,
      provenanceUnary,
      enlargedLedgerCont,
      enlargedSealCont,
      transportCont',
      routeCont',
      sealRouteCont',
      pkgSig'⟩
  exact
    ⟨rebuilt,
      enlargedLedgerUnary,
      enlargedSealUnary,
      enlargedLedgerCont,
      enlargedSealCont⟩

theorem DyadicTailBoundCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row sealRow ∧
            DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport
              route provenance localCert bundle pkg)
        (fun row : BHist => hsame row sealRow)
        (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
        hsame := by
  intro carrier
  have carrierProof := carrier
  obtain ⟨_precisionUnary, _scheduleUnary, _toleranceUnary, _readbackUnary, _sealUnary,
    _provenanceUnary, _scheduleToleranceLedger, _ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, pkgSig⟩ := carrier
  have sourceSeal :
      (fun row : BHist =>
        hsame row sealRow ∧
          DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport
            route provenance localCert bundle pkg) sealRow := by
    exact ⟨hsame_refl sealRow, carrierProof⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row sealRow ∧
            DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport
              route provenance localCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sealRow sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        constructor
        · exact hsame_trans (hsame_symm same) source.left
        · exact source.right
    }
  exact {
    core := core
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.left, pkgSig⟩
  }

theorem DyadicTailBoundCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow
                transport route provenance localCert bundle pkg)
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory ledger ∧ UnaryHistory readback)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
            Cont schedule tolerance ledger ∧ Cont ledger readback sealRow ∧
              PkgSig bundle provenance pkg := by
  intro carrier
  have carrierSource := carrier
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, sealUnary,
    _provenanceUnary, scheduleToleranceLedger, ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow
                transport route provenance localCert bundle pkg)
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory ledger ∧ UnaryHistory readback)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro (hsame_refl sealRow) carrierSource)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left (And.intro ledgerUnary readbackUnary)
    ledger_sound := by
      intro row source
      exact And.intro source.left provenancePkg
  }
  exact
    ⟨cert, precisionUnary, scheduleUnary, toleranceUnary, ledgerUnary, readbackUnary, sealUnary,
      scheduleToleranceLedger, ledgerReadbackSeal, provenancePkg⟩

end BEDC.Derived.DyadicTailBoundUp
