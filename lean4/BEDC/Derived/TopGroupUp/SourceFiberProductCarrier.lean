import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_source_fiber_product_carrier
    {group topology product inverse neighborhood ledger provenance productLedger exportLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont productLedger provenance exportLedger ->
          GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
            Cont group topology product ∧ UnaryHistory productLedger ∧
              UnaryHistory exportLedger ∧ hsame productLedger (append product neighborhood) ∧
                hsame exportLedger (append productLedger provenance) ∧ hsame provenance ledger := by
  intro package productLedgerCont exportLedgerCont
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productLedgerCont
  have exportLedgerUnary : UnaryHistory exportLedger :=
    unary_cont_closed productLedgerUnary rows.right.right.right.right exportLedgerCont
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro rows.left
        (And.intro productLedgerUnary
          (And.intro exportLedgerUnary
            (And.intro productLedgerCont
              (And.intro exportLedgerCont
                boundary.right.right.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
