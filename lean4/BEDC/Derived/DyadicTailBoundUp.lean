import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.DyadicTailBoundUp
