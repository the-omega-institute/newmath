import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_operation_ledger_consumer_boundary
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger exported : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            hsame exported consumerLedger ->
              UnaryHistory exported ∧
                hsame exported (append (append product neighborhood) (append inverse neighborhood)) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont consumerLedgerCont exportedSame
  have rows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productLedgerCont
      inverseLedgerCont consumerLedgerCont
  have exportedUnary : UnaryHistory exported :=
    unary_transport rows.right.right.left (hsame_symm exportedSame)
  have exportedReadback :
      hsame exported (append (append product neighborhood) (append inverse neighborhood)) :=
    hsame_trans exportedSame rows.right.right.right.left
  exact And.intro exportedUnary
    (And.intro exportedReadback
      (And.intro rows.right.right.right.right.left rows.right.right.right.right.right))

end BEDC.Derived.TopGroupUp
