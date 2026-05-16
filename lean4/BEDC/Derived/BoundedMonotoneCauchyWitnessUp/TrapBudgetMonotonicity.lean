import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_trap_budget_monotonicity [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      budgetRead trapRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source ledger budgetRead →
        Cont budgetRead trap trapRead →
          Cont trapRead sealRow sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory source ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory budgetRead ∧ UnaryHistory trapRead ∧
                  UnaryHistory sealRead ∧ Cont source ledger budgetRead ∧
                    Cont budgetRead trap trapRead ∧ Cont trapRead sealRow sealRead ∧
                      Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceLedgerBudget budgetTrapRead trapSealRead sealReadPkg
  obtain ⟨sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sourceUnary ledgerUnary sourceLedgerBudget
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed budgetUnary trapUnary budgetTrapRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealRead
  exact
    ⟨sourceUnary, ledgerUnary, trapUnary, sealUnary, budgetUnary, trapReadUnary, sealReadUnary,
      sourceLedgerBudget, budgetTrapRead, trapSealRead, trapSealRoute, provenancePkg, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
