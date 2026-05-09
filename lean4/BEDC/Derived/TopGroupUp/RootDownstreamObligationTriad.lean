import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootDownstreamObligationTriad
    (groupSource topologySource product inverse neighbourhood productLedger inverseLedger
      transportRows provenance : BHist) : Prop :=
  GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
    UnaryHistory neighbourhood ∧ Cont product neighbourhood productLedger ∧
      Cont inverse neighbourhood inverseLedger ∧ hsame transportRows productLedger ∧
        hsame provenance BHist.Empty

end BEDC.Derived.TopGroupUp
