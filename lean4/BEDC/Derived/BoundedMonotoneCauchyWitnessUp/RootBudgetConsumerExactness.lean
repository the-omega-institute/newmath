import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_budget_consumer_exactness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      budgetLeft budgetRight leftSeal rightSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule budgetLeft ->
        Cont source schedule budgetRight ->
          Cont budgetLeft sealRow leftSeal ->
            Cont budgetRight sealRow rightSeal ->
              PkgSig bundle leftSeal pkg ->
                PkgSig bundle rightSeal pkg ->
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory budgetLeft ∧
                    UnaryHistory budgetRight ∧ UnaryHistory leftSeal ∧
                      UnaryHistory rightSeal ∧ Cont source schedule budgetLeft ∧
                        Cont source schedule budgetRight ∧ hsame budgetLeft budgetRight ∧
                          Cont budgetLeft sealRow leftSeal ∧
                            Cont budgetRight sealRow rightSeal ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle leftSeal pkg ∧
                                  PkgSig bundle rightSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier leftBudget rightBudget leftSealRoute rightSealRoute leftPkg rightPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have leftBudgetUnary : UnaryHistory budgetLeft :=
    unary_cont_closed sourceUnary scheduleUnary leftBudget
  have rightBudgetUnary : UnaryHistory budgetRight :=
    unary_cont_closed sourceUnary scheduleUnary rightBudget
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed leftBudgetUnary sealUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed rightBudgetUnary sealUnary rightSealRoute
  have sameBudget : hsame budgetLeft budgetRight :=
    cont_deterministic leftBudget rightBudget
  exact
    ⟨sourceUnary, scheduleUnary, leftBudgetUnary, rightBudgetUnary, leftSealUnary,
      rightSealUnary, leftBudget, rightBudget, sameBudget, leftSealRoute, rightSealRoute,
      provenancePkg, leftPkg, rightPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
