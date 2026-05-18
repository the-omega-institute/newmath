import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_obligation_inventory_bridge
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          SemanticNameCert
              (fun row : BHist =>
                TopGroupRootThresholdPackage group topology product inverse neighborhood ledger
                  provenance ∧ hsame row ledger)
              (fun row : BHist =>
                hsame row ledger ∧ UnaryHistory productLedger ∧ UnaryHistory inverseLedger)
              (fun row : BHist =>
                hsame row ledger ∧ Cont product inverse ledger ∧ hsame provenance ledger)
              hsame ∧
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
              Cont product inverse ledger ∧ hsame provenance ledger := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame Cont UnaryHistory
  intro package productLedgerCont inverseLedgerCont
  have rows := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed rows.right.right.left rows.right.right.right.right.left productLedgerCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed rows.right.right.right.left rows.right.right.right.right.left inverseLedgerCont
  have operationScope := TopGroupRootThresholdPackage_operation_scope package
  obtain ⟨_operationProduct, _operationInverse, _productCont, _inverseCont,
    _productUnary, _inverseUnary, productInverseLedger, _ledgerReadback⟩ := operationScope
  have provenanceLedger : hsame provenance ledger := rows.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          TopGroupRootThresholdPackage group topology product inverse neighborhood ledger
            provenance ∧ hsame row ledger)
        (fun row : BHist =>
          hsame row ledger ∧ UnaryHistory productLedger ∧ UnaryHistory inverseLedger)
        (fun row : BHist =>
          hsame row ledger ∧ Cont product inverse ledger ∧ hsame provenance ledger)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨package, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, productLedgerUnary, inverseLedgerUnary⟩
    · intro _row source
      exact ⟨source.right, productInverseLedger, provenanceLedger⟩
  exact ⟨cert, productLedgerUnary, inverseLedgerUnary, productInverseLedger, provenanceLedger⟩

end BEDC.Derived.TopGroupUp
