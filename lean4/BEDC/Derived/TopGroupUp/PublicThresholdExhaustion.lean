import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

theorem TopGroupRootPublicThresholdPacket_public_threshold_exhaustion
    {groupSource topologySource product inverse neighbourhood ledger classifier provenance :
      BHist} :
    TopGroupRootPublicThresholdPacket groupSource topologySource product inverse neighbourhood
        ledger classifier provenance ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame ∧
        GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
          Cont product inverse ledger ∧ hsame classifier ledger ∧
            hsame provenance BHist.Empty := by
  intro packet
  have surface := TopGroupRootPublicThreshold_namecert_surface packet
  exact And.intro surface.left
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.right.left surface.right))))

end BEDC.Derived.TopGroupUp
