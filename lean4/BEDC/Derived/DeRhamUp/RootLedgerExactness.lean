import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DeRhamBoundarySourceLedgerPacket_root_ledger_exactness
    {d : BHist -> BHist} {omega eta theta zero graphLedger endpointLedger : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame zero BHist.Empty ∧
        hsame (d eta) BHist.Empty ∧ Cont theta zero graphLedger ∧
          Cont graphLedger eta endpointLedger ∧
            SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d)
              hsame := by
  intro packet
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet.left
  have cert :
      SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d) hsame :=
    DeRhamBoundary_semanticNameCert boundaryRows.right.left
  exact And.intro boundaryRows.right.left
    (And.intro boundaryRows.left
      (And.intro packet.left.right.right.right.right
        (And.intro boundaryRows.right.right
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right cert)))))

end BEDC.Derived.DeRhamUp
