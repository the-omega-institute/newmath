import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TopGroupRootThresholdPackage_source_projection_namecert_compatibility
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
        hsame (append group topology) BHist.Empty ∧ Cont group topology product ∧
          Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
            hsame provenance ledger := by
  intro package
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have sourceEmpty : hsame (append group topology) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro package.left package.right.left)
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro sourceEmpty
        (And.intro rows.left
          (And.intro rows.right.left
            (And.intro rows.right.right.left package.right.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
