import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_synchronizer_terminal_envelope
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail gridSeal terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      UnaryHistory gridBudget ->
        UnaryHistory gridClassifier ->
          UnaryHistory gridSeal ->
            Cont sealRow gridBudget gridLedger ->
              Cont gridLedger gridClassifier gridTail ->
                Cont gridTail gridSeal terminalRead ->
                  PkgSig bundle terminalRead pkg ->
                    UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory sealRow ∧
                      UnaryHistory gridBudget ∧ UnaryHistory gridLedger ∧
                        UnaryHistory gridClassifier ∧ UnaryHistory gridTail ∧
                          UnaryHistory gridSeal ∧ UnaryHistory terminalRead ∧
                            Cont trap sealRow route ∧ Cont sealRow gridBudget gridLedger ∧
                              Cont gridLedger gridClassifier gridTail ∧
                                Cont gridTail gridSeal terminalRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridClassifierUnary gridSealUnary sealGridBudget
    gridLedgerClassifier gridTailSeal terminalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed sealUnary gridBudgetUnary sealGridBudget
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridLedgerUnary gridClassifierUnary gridLedgerClassifier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed gridTailUnary gridSealUnary gridTailSeal
  exact
    ⟨sourceUnary, scheduleUnary, sealUnary, gridBudgetUnary, gridLedgerUnary,
      gridClassifierUnary, gridTailUnary, gridSealUnary, terminalUnary, trapSealRoute,
      sealGridBudget, gridLedgerClassifier, gridTailSeal, provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
