import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupObligationSurface_continuity_ledger_inventory
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      exists productLedger inverseLedger consumerLedger : BHist,
        Cont product neighborhood productLedger ∧
          Cont inverse neighborhood inverseLedger ∧
            Cont productLedger inverseLedger consumerLedger ∧
              UnaryHistory productLedger ∧
                UnaryHistory inverseLedger ∧
                  UnaryHistory consumerLedger ∧
                    hsame consumerLedger
                      (append (append product neighborhood) (append inverse neighborhood)) ∧
                      hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package
  let productLedger := append product neighborhood
  let inverseLedger := append inverse neighborhood
  let consumerLedger := append productLedger inverseLedger
  have productRow : Cont product neighborhood productLedger := by
    rfl
  have inverseRow : Cont inverse neighborhood inverseLedger := by
    rfl
  have consumerRow : Cont productLedger inverseLedger consumerLedger := by
    rfl
  have rows :=
    TopGroupRootThresholdPackage_operation_ledger_obligation package productRow inverseRow
      consumerRow
  exact Exists.intro productLedger
    (Exists.intro inverseLedger
      (Exists.intro consumerLedger
        (And.intro productRow
          (And.intro inverseRow
            (And.intro consumerRow
              (And.intro rows.left
                (And.intro rows.right.left
                  (And.intro rows.right.right.left
                    (And.intro rows.right.right.right.left
                      (And.intro rows.right.right.right.right.left
                        rows.right.right.right.right.right))))))))))

end BEDC.Derived.TopGroupUp
