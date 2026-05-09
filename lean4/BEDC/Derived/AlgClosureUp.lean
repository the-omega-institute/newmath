import BEDC.FKernel.Cont

namespace BEDC.Derived.AlgClosureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def AlgClosureCarrierPacket
    (fieldExt polynomial root transport ledger provenance : BHist) : Prop :=
  hsame transport root ∧ Cont polynomial root ledger ∧ Cont fieldExt ledger provenance

theorem AlgClosureCarrierPacket_source_obligation
    {fieldExt polynomial root transport ledger provenance : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance →
      hsame transport root ∧ Cont polynomial root ledger ∧
        Cont fieldExt ledger provenance ∧ hsame provenance (append fieldExt ledger) := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right packet.right.right))

end BEDC.Derived.AlgClosureUp
