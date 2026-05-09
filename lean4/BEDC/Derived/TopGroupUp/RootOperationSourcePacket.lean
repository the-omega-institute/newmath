import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootOperationSourcePacket [AskSetup] [PackageSetup]
    (group topology product inverse neighborhood ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory group ∧ UnaryHistory topology ∧ UnaryHistory product ∧ UnaryHistory inverse ∧
    UnaryHistory neighborhood ∧ UnaryHistory provenance ∧ Cont product inverse ledger ∧
      Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem TopGroupRootOperationSourcePacket_cont_pkg_rows [AskSetup] [PackageSetup]
    {group topology product inverse neighborhood ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TopGroupRootOperationSourcePacket group topology product inverse neighborhood ledger
        provenance endpoint bundle pkg ->
      Cont product inverse ledger ∧ Cont provenance ledger endpoint ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have productInverseLedger : Cont product inverse ledger :=
    packet.right.right.right.right.right.right.left
  have provenanceLedgerEndpoint : Cont provenance ledger endpoint :=
    packet.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left productInverseLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed packet.right.right.right.right.right.left ledgerUnary
      provenanceLedgerEndpoint
  exact And.intro productInverseLedger
    (And.intro provenanceLedgerEndpoint
      (And.intro ledgerUnary
        (And.intro endpointUnary packet.right.right.right.right.right.right.right.right)))

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
