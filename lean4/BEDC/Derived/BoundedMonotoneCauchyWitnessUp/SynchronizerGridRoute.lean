import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_synchronizer_grid_route
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail rootRead gridSelectorRead gridLedgerRead
      gridClassifierRead gridTailRead realRead synchronizerRead : BHist}
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
                          Cont rootRead route synchronizerRead →
                            PkgSig bundle realRead pkg →
                              PkgSig bundle synchronizerRead pkg →
                                UnaryHistory rootRead ∧ UnaryHistory gridSelectorRead ∧
                                  UnaryHistory gridLedgerRead ∧
                                    UnaryHistory gridClassifierRead ∧
                                      UnaryHistory gridTailRead ∧ UnaryHistory realRead ∧
                                        UnaryHistory synchronizerRead ∧
                                          Cont rootRead gridBudget gridSelectorRead ∧
                                            Cont gridSelectorRead gridLedger gridLedgerRead ∧
                                              Cont gridLedgerRead gridClassifier
                                                gridClassifierRead ∧
                                                Cont gridClassifierRead gridTail gridTailRead ∧
                                                  Cont gridTailRead sealRow realRead ∧
                                                    Cont rootRead route synchronizerRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle realRead pkg ∧
                                                          PkgSig bundle synchronizerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridLedgerUnary gridClassifierUnary gridTailUnary
    sourceRegularRoot rootGridBudget gridSelectorGridLedger gridLedgerGridClassifier
    gridClassifierGridTail gridTailSealReal rootRouteSynchronizer realPkg synchronizerPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
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
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed gridTailReadUnary sealUnary gridTailSealReal
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary _trapSealRoute
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed rootUnary routeUnary rootRouteSynchronizer
  exact
    ⟨rootUnary, gridSelectorUnary, gridLedgerReadUnary, gridClassifierReadUnary,
      gridTailReadUnary, realReadUnary, synchronizerUnary, rootGridBudget,
      gridSelectorGridLedger, gridLedgerGridClassifier, gridClassifierGridTail, gridTailSealReal,
      rootRouteSynchronizer, provenancePkg, realPkg, synchronizerPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
