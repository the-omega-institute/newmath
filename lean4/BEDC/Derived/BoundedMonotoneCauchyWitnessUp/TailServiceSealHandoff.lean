import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_service_seal_handoff [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead modulusRead budgetRead trapRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness modulusRead →
          Cont modulusRead ledger budgetRead →
            Cont budgetRead trap trapRead →
              Cont trapRead sealRow sealRead →
                PkgSig bundle sealRead pkg →
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                    UnaryHistory ledger ∧ UnaryHistory trap ∧ UnaryHistory sealRow ∧
                      UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory budgetRead ∧ UnaryHistory trapRead ∧
                          UnaryHistory sealRead ∧ Cont source schedule windowRead ∧
                            Cont windowRead witness modulusRead ∧
                              Cont modulusRead ledger budgetRead ∧
                                Cont budgetRead trap trapRead ∧
                                  Cont trapRead sealRow sealRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessModulus modulusLedgerBudget budgetTrap
    trapSeal sealPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessModulus
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed modulusUnary ledgerUnary modulusLedgerBudget
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed budgetUnary trapUnary budgetTrap
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapSeal
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      windowUnary, modulusUnary, budgetUnary, trapReadUnary, sealReadUnary,
      sourceScheduleWindow, windowWitnessModulus, modulusLedgerBudget, budgetTrap, trapSeal,
      provenancePkg, sealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
