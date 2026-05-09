import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootPublicThreshold_frontier_threshold
    {groupSource topologySource product inverse neighbourhood ledger classifier provenance :
      BHist} :
    TopGroupRootPublicThresholdPacket groupSource topologySource product inverse neighbourhood
        ledger classifier provenance ->
      exists threshold : BHist,
        Cont ledger classifier threshold ∧ hsame threshold (append ledger classifier) ∧
          SemanticNameCert (fun row : BHist => hsame row provenance)
            (fun row : BHist => hsame row provenance)
            (fun row : BHist => hsame row provenance) hsame ∧
            hsame classifier ledger ∧ hsame provenance BHist.Empty := by
  intro packet
  let threshold := append ledger classifier
  have thresholdRow : Cont ledger classifier threshold := by
    rfl
  have thresholdExact : hsame threshold (append ledger classifier) := by
    rfl
  have publicCert :=
    TopGroupRootPublicThreshold_namecert_surface
      (groupSource := groupSource) (topologySource := topologySource) (product := product)
      (inverse := inverse) (neighbourhood := neighbourhood) (ledger := ledger)
      (classifier := classifier) (provenance := provenance) packet
  exact Exists.intro threshold
    (And.intro thresholdRow
      (And.intro thresholdExact
        (And.intro publicCert.left
          (And.intro packet.right.right.right.right.left
            packet.right.right.right.right.right))))

end BEDC.Derived.TopGroupUp
