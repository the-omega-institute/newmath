import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_budget_cofinal_readback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead budgetRead gridBudget gridLedger gridClassifier gridTail terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead ledger budgetRead →
          UnaryHistory gridBudget →
            UnaryHistory gridClassifier →
              Cont sealRow gridBudget gridLedger →
                Cont gridLedger gridClassifier gridTail →
                  Cont gridTail budgetRead terminalRead →
                    PkgSig bundle terminalRead pkg →
                      UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                        UnaryHistory sealRow ∧ UnaryHistory envelopeRead ∧
                          UnaryHistory budgetRead ∧ UnaryHistory gridLedger ∧
                            UnaryHistory gridTail ∧ UnaryHistory terminalRead ∧
                              Cont source schedule envelopeRead ∧
                                Cont envelopeRead ledger budgetRead ∧
                                  Cont sealRow gridBudget gridLedger ∧
                                    Cont gridLedger gridClassifier gridTail ∧
                                      Cont gridTail budgetRead terminalRead ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleEnvelope envelopeLedgerBudget gridBudgetUnary gridClassifierUnary
    sealGridBudget gridLedgerClassifier gridTailBudget terminalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed envelopeUnary ledgerUnary envelopeLedgerBudget
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed sealUnary gridBudgetUnary sealGridBudget
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridLedgerUnary gridClassifierUnary gridLedgerClassifier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed gridTailUnary budgetUnary gridTailBudget
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, sealUnary, envelopeUnary, budgetUnary,
      gridLedgerUnary, gridTailUnary, terminalUnary, sourceScheduleEnvelope,
      envelopeLedgerBudget, sealGridBudget, gridLedgerClassifier, gridTailBudget, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
