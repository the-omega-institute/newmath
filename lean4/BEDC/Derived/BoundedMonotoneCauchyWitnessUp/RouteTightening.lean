import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_route_tightening [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead budgetRead gridBudget gridLedger gridClassifier gridTail realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead ledger budgetRead →
          UnaryHistory gridBudget →
            UnaryHistory gridClassifier →
              Cont budgetRead gridBudget gridLedger →
                Cont gridLedger gridClassifier gridTail →
                  Cont gridTail trap realRead →
                    PkgSig bundle realRead pkg →
                      UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                        UnaryHistory trap ∧ UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                          UnaryHistory gridLedger ∧ UnaryHistory gridTail ∧
                            UnaryHistory realRead ∧ Cont source schedule tailRead ∧
                              Cont tailRead ledger budgetRead ∧
                                Cont budgetRead gridBudget gridLedger ∧
                                  Cont gridLedger gridClassifier gridTail ∧
                                    Cont gridTail trap realRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailLedgerBudget gridBudgetUnary gridClassifierUnary
    budgetGrid gridLedgerClassifier gridTailTrap realPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerBudget
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed budgetUnary gridBudgetUnary budgetGrid
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridLedgerUnary gridClassifierUnary gridLedgerClassifier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed gridTailUnary trapUnary gridTailTrap
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, trapUnary, tailUnary, budgetUnary,
      gridLedgerUnary, gridTailUnary, realUnary, sourceScheduleTail, tailLedgerBudget,
      budgetGrid, gridLedgerClassifier, gridTailTrap, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
