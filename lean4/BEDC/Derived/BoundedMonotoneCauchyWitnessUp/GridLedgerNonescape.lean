import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_ledger_nonescape [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail rootRead gridSelectorRead gridLedgerRead
      gridClassifierRead gridTailRead realRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      UnaryHistory gridBudget ->
        UnaryHistory gridLedger ->
          UnaryHistory gridClassifier ->
            UnaryHistory gridTail ->
              Cont source regular rootRead ->
                Cont rootRead gridBudget gridSelectorRead ->
                  Cont gridSelectorRead gridLedger gridLedgerRead ->
                    Cont gridLedgerRead gridClassifier gridClassifierRead ->
                      Cont gridClassifierRead gridTail gridTailRead ->
                        Cont gridTailRead sealRow realRead ->
                          Cont realRead provenance auditRead ->
                            PkgSig bundle realRead pkg ->
                              PkgSig bundle auditRead pkg ->
                                UnaryHistory gridSelectorRead ∧
                                  UnaryHistory gridLedgerRead ∧
                                    UnaryHistory gridClassifierRead ∧
                                      UnaryHistory gridTailRead ∧ UnaryHistory realRead ∧
                                        UnaryHistory auditRead ∧
                                          Cont rootRead gridBudget gridSelectorRead ∧
                                            Cont gridSelectorRead gridLedger
                                              gridLedgerRead ∧
                                              Cont gridLedgerRead gridClassifier
                                                gridClassifierRead ∧
                                                Cont gridClassifierRead gridTail
                                                  gridTailRead ∧
                                                  Cont gridTailRead sealRow realRead ∧
                                                    Cont realRead provenance auditRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle realRead pkg ∧
                                                          PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridLedgerUnary gridClassifierUnary gridTailUnary
    sourceRegularRoot rootGridBudget gridSelectorGridLedger gridLedgerGridClassifier
    gridClassifierGridTail gridTailSeal realProvenanceAudit realPkg auditPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
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
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed realUnary provenanceUnary realProvenanceAudit
  exact
    ⟨gridSelectorUnary, gridLedgerReadUnary, gridClassifierReadUnary, gridTailReadUnary,
      realUnary, auditUnary, rootGridBudget, gridSelectorGridLedger,
      gridLedgerGridClassifier, gridClassifierGridTail, gridTailSeal, realProvenanceAudit,
      provenancePkg, realPkg, auditPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
