import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_readback_stability [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      source' regular' schedule' witness' ledger' trap' sealRow' transport' route' provenance'
      localCert' windowRead windowRead' sealRead sealRead' completionRead completionRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      BoundedMonotoneCauchyWitnessCarrier source' regular' schedule' witness' ledger' trap'
        sealRow' transport' route' provenance' localCert' bundle pkg →
        hsame source source' →
          hsame schedule schedule' →
            hsame witness witness' →
              hsame ledger ledger' →
                hsame sealRow sealRow' →
                  hsame provenance provenance' →
                    Cont source schedule windowRead →
                      Cont source' schedule' windowRead' →
                        Cont windowRead ledger sealRead →
                          Cont windowRead' ledger' sealRead' →
                            Cont sealRead provenance completionRead →
                              Cont sealRead' provenance' completionRead' →
                                PkgSig bundle completionRead pkg →
                                  PkgSig bundle completionRead' pkg →
                                    hsame windowRead windowRead' ∧ hsame sealRead sealRead' ∧
                                      hsame completionRead completionRead' ∧
                                        UnaryHistory completionRead ∧
                                          UnaryHistory completionRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier carrier' sameSource sameSchedule _sameWitness sameLedger _sameSealRow
    sameProvenance sourceScheduleWindow sourceScheduleWindow' windowLedgerSeal
    windowLedgerSeal' sealProvenanceCompletion sealProvenanceCompletion' _completionPkg
    _completionPkg'
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  obtain ⟨_sourceUnary', _regularUnary', _scheduleUnary', _witnessUnary', _ledgerUnary',
    _trapUnary', _sealUnary', provenanceUnary', _sourceScheduleRegular',
    _regularWitnessTrap', _trapSealRoute', _transportLocalCertRoute',
    _routeProvenanceSeal', _provenancePkg'⟩ := carrier'
  have sameWindow : hsame windowRead windowRead' :=
    cont_respects_hsame sameSource sameSchedule sourceScheduleWindow sourceScheduleWindow'
  have sameSeal : hsame sealRead sealRead' :=
    cont_respects_hsame sameWindow sameLedger windowLedgerSeal windowLedgerSeal'
  have sameCompletion : hsame completionRead completionRead' :=
    cont_respects_hsame sameSeal sameProvenance sealProvenanceCompletion
      sealProvenanceCompletion'
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerSeal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceCompletion
  have completionUnary' : UnaryHistory completionRead' :=
    unary_transport completionUnary sameCompletion
  exact ⟨sameWindow, sameSeal, sameCompletion, completionUnary, completionUnary'⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
