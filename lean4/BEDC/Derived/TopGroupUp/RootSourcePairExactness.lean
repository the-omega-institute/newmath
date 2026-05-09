import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootOperationSourcePacket_source_pair_exactness
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory neighborhood ∧
        Cont group topology product ∧ hsame inverse BHist.Empty ∧ Cont product inverse ledger ∧
          hsame provenance ledger := by
  intro package
  exact
    ⟨package.left, package.right.left, package.right.right.left,
      package.right.right.right.left, package.right.right.right.right.left,
      package.right.right.right.right.right.left,
      package.right.right.right.right.right.right⟩

end BEDC.Derived.TopGroupUp
