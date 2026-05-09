import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DeRhamBoundarySourceLedgerPacket_bridge_classifier_source_scope
    {d : BHist -> BHist} {omega eta theta theta' zero graphLedger endpointLedger : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      hsame theta' theta ->
        SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d) hsame ∧
          DeRhamBoundary d theta' ∧ hsame theta' zero ∧ hsame (d eta) BHist.Empty ∧
            hsame zero BHist.Empty ∧ Cont theta zero graphLedger ∧
              Cont graphLedger eta endpointLedger := by
  intro packet sameTheta'
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet.left
  have boundaryTheta' : DeRhamBoundary d theta' := by
    cases boundaryRows.right.left with
    | intro preimage sameThetaPreimage =>
        exact Exists.intro preimage (hsame_trans sameTheta' sameThetaPreimage)
  have cert :
      SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d) hsame :=
    DeRhamBoundary_semanticNameCert boundaryTheta'
  exact And.intro cert
    (And.intro boundaryTheta'
      (And.intro (hsame_trans sameTheta' boundaryRows.left)
        (And.intro boundaryRows.right.right
          (And.intro packet.left.right.right.right.right
            (And.intro packet.right.right.right.left packet.right.right.right.right)))))

end BEDC.Derived.DeRhamUp
