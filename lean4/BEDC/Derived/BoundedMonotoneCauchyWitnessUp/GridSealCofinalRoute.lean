import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_seal_cofinal_route [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail rootRead gridSelectorRead gridLedgerRead
      gridClassifierRead gridTailRead realRead cofinalRead : BHist}
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
                          Cont realRead provenance cofinalRead →
                            PkgSig bundle realRead pkg →
                              PkgSig bundle cofinalRead pkg →
                                SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row cofinalRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row cofinalRead ∧
                                          Cont rootRead gridBudget gridSelectorRead ∧
                                            Cont gridTailRead sealRow realRead ∧
                                              Cont realRead provenance cofinalRead)
                                      (fun row : BHist =>
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle cofinalRead pkg ∧
                                            hsame row cofinalRead)
                                      hsame ∧
                                  UnaryHistory cofinalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier gridBudgetUnary gridLedgerUnary gridClassifierUnary gridTailUnary
    sourceRegularRoot rootGridBudget gridSelectorGridLedger gridLedgerGridClassifier
    gridClassifierGridTail gridTailSeal realProvenanceCofinal _realPkg cofinalPkg
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
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed realUnary provenanceUnary realProvenanceCofinal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cofinalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cofinalRead ∧ Cont rootRead gridBudget gridSelectorRead ∧
              Cont gridTailRead sealRow realRead ∧ Cont realRead provenance cofinalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle cofinalRead pkg ∧
              hsame row cofinalRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro cofinalRead (And.intro (hsame_refl cofinalRead) cofinalUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro row source
      exact
        And.intro source.left
          (And.intro rootGridBudget
            (And.intro gridTailSeal realProvenanceCofinal))
    ledger_sound := by
      intro row source
      exact And.intro provenancePkg (And.intro cofinalPkg source.left)
  }
  exact And.intro cert cofinalUnary

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
