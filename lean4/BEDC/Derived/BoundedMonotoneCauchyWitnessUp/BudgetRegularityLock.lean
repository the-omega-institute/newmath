import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_budget_regularity_lock [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      budgetRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont schedule ledger budgetRead ->
        Cont budgetRead witness tailRead ->
          PkgSig bundle budgetRead pkg ->
            PkgSig bundle tailRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory budgetRead ∧
                  UnaryHistory tailRead ∧ Cont source schedule regular ∧
                    Cont schedule ledger budgetRead ∧ Cont budgetRead witness tailRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg ∧
                        PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleLedgerBudget budgetWitnessTail budgetPkg tailPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerBudget
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed budgetUnary witnessUnary budgetWitnessTail
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, budgetUnary,
      tailUnary, sourceScheduleRegular, scheduleLedgerBudget, budgetWitnessTail,
      provenancePkg, budgetPkg, tailPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
