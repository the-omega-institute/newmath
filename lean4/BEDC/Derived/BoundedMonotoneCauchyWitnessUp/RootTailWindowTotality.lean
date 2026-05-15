import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_tail_window_totality [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead ledgerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead ledger ledgerRead →
          Cont ledgerRead sealRow sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory ledger ∧ UnaryHistory tailRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory sealRead ∧ Cont source schedule tailRead ∧
                    Cont tailRead ledger ledgerRead ∧ Cont ledgerRead sealRow sealRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailLedgerRead ledgerSealRead sealReadPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerReadUnary sealUnary ledgerSealRead
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, tailUnary, ledgerReadUnary,
      sealReadUnary, sourceScheduleTail, tailLedgerRead, ledgerSealRead, provenancePkg,
      sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
