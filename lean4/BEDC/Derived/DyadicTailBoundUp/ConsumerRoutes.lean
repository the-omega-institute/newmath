import BEDC.Derived.DyadicTailBoundUp

namespace BEDC.Derived.DyadicTailBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicTailBoundCarrier_cauchy_rate_consumer_route [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      rateRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      Cont ledger readback rateRead ->
        Cont rateRead sealRow sealRead ->
          PkgSig bundle rateRead pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
                UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                  UnaryHistory rateRead ∧ UnaryHistory sealRead ∧
                    Cont schedule tolerance ledger ∧ Cont ledger readback rateRead ∧
                      Cont rateRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle rateRead pkg ∧ PkgSig bundle sealRead pkg := by
  intro carrier ledgerReadbackRate rateSealRead ratePkg sealPkg
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, sealUnary,
    _provenanceUnary, scheduleToleranceLedger, _ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed ledgerUnary readbackUnary ledgerReadbackRate
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rateUnary sealUnary rateSealRead
  exact
    ⟨precisionUnary,
      scheduleUnary,
      toleranceUnary,
      ledgerUnary,
      readbackUnary,
      sealUnary,
      rateUnary,
      sealReadUnary,
      scheduleToleranceLedger,
      ledgerReadbackRate,
      rateSealRead,
      provenancePkg,
      ratePkg,
      sealPkg⟩

theorem DyadicTailBoundCarrier_schedule_monotone_consumer [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance localCert
      precision' schedule' ledger' readback' sealRow' transport' route' consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
        provenance localCert bundle pkg ->
      hsame precision precision' ->
        hsame schedule schedule' ->
          Cont schedule' tolerance ledger' ->
            Cont ledger' readback' sealRow' ->
              Cont ledger' readback' consumer ->
                Cont precision' sealRow' transport' ->
                  Cont transport' localCert route' ->
                    Cont route' provenance sealRow' ->
                      hsame readback readback' ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle consumer pkg ->
                            DyadicTailBoundCarrier precision' schedule' tolerance ledger' readback'
                                sealRow' transport' route' provenance localCert bundle pkg ∧
                              UnaryHistory ledger' ∧ UnaryHistory consumer ∧
                                hsame ledger ledger' ∧ hsame sealRow sealRow' ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  intro carrier samePrecision sameSchedule scheduleToleranceLedger' ledgerReadbackSeal'
    ledgerReadbackConsumer precisionSealTransport' transportLocalRoute' routeProvenanceSeal'
    sameReadback provenancePkg' consumerPkg
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    provenanceUnary, scheduleToleranceLedger, ledgerReadbackSeal, _precisionSealTransport,
    _transportLocalRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed scheduleUnary' toleranceUnary scheduleToleranceLedger'
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed ledgerUnary' readbackUnary' ledgerReadbackSeal'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary' readbackUnary' ledgerReadbackConsumer
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSchedule (hsame_refl tolerance) scheduleToleranceLedger
      scheduleToleranceLedger'
  have sameSeal : hsame sealRow sealRow' :=
    cont_respects_hsame sameLedger sameReadback ledgerReadbackSeal ledgerReadbackSeal'
  have rebuilt :
      DyadicTailBoundCarrier precision' schedule' tolerance ledger' readback' sealRow'
          transport' route' provenance localCert bundle pkg :=
    ⟨precisionUnary',
      scheduleUnary',
      toleranceUnary,
      readbackUnary',
      sealUnary',
      provenanceUnary,
      scheduleToleranceLedger',
      ledgerReadbackSeal',
      precisionSealTransport',
      transportLocalRoute',
      routeProvenanceSeal',
      provenancePkg'⟩
  exact
    ⟨rebuilt,
      ledgerUnary',
      consumerUnary,
      sameLedger,
      sameSeal,
      provenancePkg',
      consumerPkg⟩

end BEDC.Derived.DyadicTailBoundUp
