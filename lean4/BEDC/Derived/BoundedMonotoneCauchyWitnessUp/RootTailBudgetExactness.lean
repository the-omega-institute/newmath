import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_tail_budget_exactness [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead budgetRead ledgerRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source regular rootRead →
        Cont rootRead ledger budgetRead →
          Cont budgetRead witness ledgerRead →
            Cont ledgerRead trap tailRead →
              Cont tailRead sealRow sealRead →
                PkgSig bundle sealRead pkg →
                  UnaryHistory rootRead ∧ UnaryHistory budgetRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                      Cont source regular rootRead ∧ Cont rootRead ledger budgetRead ∧
                        Cont budgetRead witness ledgerRead ∧ Cont ledgerRead trap tailRead ∧
                          Cont tailRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularRoot rootLedgerBudget budgetWitnessLedger ledgerTrapTail
    tailSealRead sealPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed rootUnary ledgerUnary rootLedgerBudget
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed budgetUnary witnessUnary budgetWitnessLedger
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed ledgerReadUnary trapUnary ledgerTrapTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealUnary tailSealRead
  exact
    ⟨rootUnary, budgetUnary, ledgerReadUnary, tailUnary, sealReadUnary, sourceRegularRoot,
      rootLedgerBudget, budgetWitnessLedger, ledgerTrapTail, tailSealRead, provenancePkg,
      sealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
