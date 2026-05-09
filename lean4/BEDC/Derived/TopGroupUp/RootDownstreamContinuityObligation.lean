import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_root_downstream_continuity_obligation
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
            Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
              Cont product inverse ledger ∧ hsame ledger (append product inverse) ∧
                hsame provenance ledger := by
  intro package productRow inverseRow
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left productRow
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseRow
  exact And.intro productLedgerUnary
    (And.intro inverseLedgerUnary
      (And.intro productRow
        (And.intro inverseRow
          (And.intro package.right.right.right.right.right.left
            (And.intro boundary.right.right.right.right.right.right.left
              boundary.right.right.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
