import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootOperationSourcePacket_root_source_pair_exactness
    {group topology product inverse neighborhood ledger provenance endpoint : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont ledger provenance endpoint ->
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
          Cont group topology product ∧ Cont product inverse ledger ∧
            Cont ledger provenance endpoint ∧ UnaryHistory endpoint ∧
              hsame endpoint (append ledger provenance) := by
  intro package endpointCont
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rows.right.right.right.left rows.right.right.right.right endpointCont
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro rows.left
        (And.intro rows.right.left
          (And.intro endpointCont
            (And.intro endpointUnary endpointCont)))))

end BEDC.Derived.TopGroupUp
