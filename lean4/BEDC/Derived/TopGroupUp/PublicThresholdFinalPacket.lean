import BEDC.Derived.TopGroupUp.PublicThresholdFrontier

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootPublicThresholdFinalPacket
    (groupSource topologySource product inverse neighbourhood ledger classifier provenance :
      BHist) : Prop :=
  GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
    Cont product inverse ledger ∧ hsame neighbourhood BHist.Empty ∧
      hsame classifier ledger ∧ hsame provenance BHist.Empty ∧
        hsame (append (append groupSource topologySource) (append product inverse)) ledger

end BEDC.Derived.TopGroupUp
