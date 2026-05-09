import BEDC.Derived.GroupUp
import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopgroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootPublicThresholdPacket
    (groupSource topologySource product inverse neighbourhood ledger classifier provenance :
      BHist) : Prop :=
  GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
    Cont product inverse ledger ∧ hsame neighbourhood BHist.Empty ∧
      hsame classifier ledger ∧ hsame provenance BHist.Empty

end BEDC.Derived.TopgroupUp
