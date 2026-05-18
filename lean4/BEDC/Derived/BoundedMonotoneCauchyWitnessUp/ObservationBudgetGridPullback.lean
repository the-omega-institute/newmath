import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_observation_budget_grid_pullback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget _gridLedger gridClassifier _gridTail observationRead pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridClassifier →
      Cont schedule ledger gridBudget →
        Cont gridBudget gridClassifier observationRead →
          Cont observationRead sealRow pullbackRead →
            PkgSig bundle pullbackRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                UnaryHistory gridBudget ∧ UnaryHistory observationRead ∧
                  UnaryHistory pullbackRead ∧ Cont schedule ledger gridBudget ∧
                    Cont gridBudget gridClassifier observationRead ∧
                      Cont observationRead sealRow pullbackRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle pullbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridClassifierUnary scheduleLedgerGrid gridClassifierObservation observationSealPullback
    pullbackPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary,
    _trapUnary, sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have gridBudgetUnary : UnaryHistory gridBudget :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerGrid
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed gridBudgetUnary gridClassifierUnary gridClassifierObservation
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed observationUnary sealUnary observationSealPullback
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, gridBudgetUnary, observationUnary,
      pullbackUnary, scheduleLedgerGrid, gridClassifierObservation, observationSealPullback,
      provenancePkg, pullbackPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
