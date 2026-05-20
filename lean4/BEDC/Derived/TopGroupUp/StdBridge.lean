import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupUp_StdBridge
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          SemanticNameCert
              (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row ledger ∨ hsame row productLedger ∨ hsame row inverseLedger)
              (fun row : BHist => hsame row provenance ∧ Cont product inverse ledger)
              hsame ∧
            GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
              UnaryHistory product ∧ UnaryHistory inverse ∧ UnaryHistory productLedger ∧
                UnaryHistory inverseLedger ∧ UnaryHistory ledger ∧ Cont product inverse ledger ∧
                  Cont product neighborhood productLedger ∧
                    Cont inverse neighborhood inverseLedger ∧
                      hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro package productLedgerRoute inverseLedgerRoute
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have groupCarrier : GroupSingletonCarrier group := boundary.left
  have topologyCarrier : TopologySingletonCarrier topology := boundary.right.left
  have productUnary : UnaryHistory product := boundary.right.right.left
  have inverseUnary : UnaryHistory inverse := boundary.right.right.right.left
  have neighborhoodUnary : UnaryHistory neighborhood := boundary.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger := boundary.right.right.right.right.right.left
  have ledgerSameProductInverse : hsame ledger (append product inverse) :=
    boundary.right.right.right.right.right.right.left
  have provenanceSameLedger : hsame provenance ledger :=
    boundary.right.right.right.right.right.right.right
  have productInverseLedger : Cont product inverse ledger :=
    ledgerSameProductInverse
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport ledgerUnary (hsame_symm provenanceSameLedger)
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed productUnary neighborhoodUnary productLedgerRoute
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed inverseUnary neighborhoodUnary inverseLedgerRoute
  have sourceAtProvenance : hsame provenance provenance ∧ UnaryHistory provenance :=
    ⟨hsame_refl provenance, provenanceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ledger ∨ hsame row productLedger ∨ hsame row inverseLedger)
          (fun row : BHist => hsame row provenance ∧ Cont product inverse ledger)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance sourceAtProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inl (hsame_trans source.left provenanceSameLedger)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, productInverseLedger⟩
  }
  exact
    ⟨cert, groupCarrier, topologyCarrier, productUnary, inverseUnary, productLedgerUnary,
      inverseLedgerUnary, ledgerUnary, productInverseLedger, productLedgerRoute,
      inverseLedgerRoute, ledgerSameProductInverse, provenanceSameLedger⟩

end BEDC.Derived.TopGroupUp
