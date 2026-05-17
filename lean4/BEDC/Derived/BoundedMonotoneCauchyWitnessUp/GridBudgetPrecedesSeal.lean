import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_budget_precedes_seal [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail gridRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule gridBudget →
        Cont gridBudget ledger gridLedger →
          Cont gridLedger regular gridClassifier →
            Cont gridClassifier trap gridTail →
              Cont gridTail sealRow gridRead →
                PkgSig bundle gridRead pkg →
                  UnaryHistory gridBudget ∧ UnaryHistory gridLedger ∧
                    UnaryHistory gridClassifier ∧ UnaryHistory gridTail ∧
                      UnaryHistory gridRead ∧ Cont gridBudget ledger gridLedger ∧
                        Cont gridTail sealRow gridRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle gridRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleGrid gridBudgetLedger gridLedgerRegular gridClassifierTrap
    gridTailSeal gridReadPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have gridBudgetUnary : UnaryHistory gridBudget :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleGrid
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed gridBudgetUnary ledgerUnary gridBudgetLedger
  have gridClassifierUnary : UnaryHistory gridClassifier :=
    unary_cont_closed gridLedgerUnary regularUnary gridLedgerRegular
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridClassifierUnary trapUnary gridClassifierTrap
  have gridReadUnary : UnaryHistory gridRead :=
    unary_cont_closed gridTailUnary sealUnary gridTailSeal
  exact
    ⟨gridBudgetUnary, gridLedgerUnary, gridClassifierUnary, gridTailUnary, gridReadUnary,
      gridBudgetLedger, gridTailSeal, provenancePkg, gridReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
