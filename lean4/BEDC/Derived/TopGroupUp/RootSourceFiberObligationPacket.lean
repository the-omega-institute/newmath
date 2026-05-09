import BEDC.Derived.TopGroupUp
import BEDC.FKernel.Package

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootSourceFiberObligationPacket [AskSetup] [PackageSetup]
    (groupSource topologySource product inverse neighbourhood classifier ledger provenance :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
    UnaryHistory product ∧ UnaryHistory inverse ∧ UnaryHistory neighbourhood ∧
      hsame classifier (append groupSource topologySource) ∧ Cont product inverse ledger ∧
        PkgSig bundle provenance pkg

end BEDC.Derived.TopGroupUp
