import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_route_compatibility [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail rootRead gridSelectorRead gridLedgerRead
      gridClassifierRead gridTailRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridBudget →
        UnaryHistory gridLedger →
          UnaryHistory gridClassifier →
            UnaryHistory gridTail →
              Cont source regular rootRead →
                Cont rootRead gridBudget gridSelectorRead →
                  Cont gridSelectorRead gridLedger gridLedgerRead →
                    Cont gridLedgerRead gridClassifier gridClassifierRead →
                      Cont gridClassifierRead gridTail gridTailRead →
                        Cont gridTailRead sealRow realRead →
                          PkgSig bundle realRead pkg →
                            UnaryHistory rootRead ∧ UnaryHistory gridSelectorRead ∧
                              UnaryHistory gridLedgerRead ∧ UnaryHistory gridClassifierRead ∧
                                UnaryHistory gridTailRead ∧ UnaryHistory realRead ∧
                                  Cont source regular rootRead ∧
                                    Cont rootRead gridBudget gridSelectorRead ∧
                                      Cont gridSelectorRead gridLedger gridLedgerRead ∧
                                        Cont gridLedgerRead gridClassifier gridClassifierRead ∧
                                          Cont gridClassifierRead gridTail gridTailRead ∧
                                            Cont gridTailRead sealRow realRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridLedgerUnary gridClassifierUnary gridTailUnary
    sourceRegularRoot rootGridBudget gridSelectorGridLedger gridLedgerGridClassifier
    gridClassifierGridTail gridTailSeal realPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have gridSelectorUnary : UnaryHistory gridSelectorRead :=
    unary_cont_closed rootUnary gridBudgetUnary rootGridBudget
  have gridLedgerReadUnary : UnaryHistory gridLedgerRead :=
    unary_cont_closed gridSelectorUnary gridLedgerUnary gridSelectorGridLedger
  have gridClassifierReadUnary : UnaryHistory gridClassifierRead :=
    unary_cont_closed gridLedgerReadUnary gridClassifierUnary gridLedgerGridClassifier
  have gridTailReadUnary : UnaryHistory gridTailRead :=
    unary_cont_closed gridClassifierReadUnary gridTailUnary gridClassifierGridTail
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed gridTailReadUnary sealUnary gridTailSeal
  exact
    ⟨rootUnary, gridSelectorUnary, gridLedgerReadUnary, gridClassifierReadUnary,
      gridTailReadUnary, realUnary, sourceRegularRoot, rootGridBudget, gridSelectorGridLedger,
      gridLedgerGridClassifier, gridClassifierGridTail, gridTailSeal, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
