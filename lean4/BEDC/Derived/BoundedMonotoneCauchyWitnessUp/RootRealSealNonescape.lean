import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_real_seal_nonescape
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead ledgerRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead ledger ledgerRead →
          Cont ledgerRead sealRow realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                UnaryHistory sealRow ∧ UnaryHistory windowRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory realRead ∧ Cont source schedule windowRead ∧
                    Cont windowRead ledger ledgerRead ∧ Cont ledgerRead sealRow realRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowLedgerRead ledgerSealReal realPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed ledgerReadUnary sealUnary ledgerSealReal
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, sealUnary, windowUnary, ledgerReadUnary,
      realReadUnary, sourceScheduleWindow, windowLedgerRead, ledgerSealReal, provenancePkg,
      realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
