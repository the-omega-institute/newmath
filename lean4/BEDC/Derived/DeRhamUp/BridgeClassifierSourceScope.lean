import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DeRhamBoundarySourceLedgerPacket_bridge_classifier_source_scope
    {d : BHist -> BHist}
    {omega eta eta' theta theta' zero zero' graphLedger endpointLedger graphLedger'
      endpointLedger' : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      hsame theta' theta ->
        hsame zero zero' ->
          hsame eta eta' ->
            Cont theta' zero' graphLedger' ->
              Cont graphLedger' eta' endpointLedger' ->
                DeRhamBoundary d theta' ∧ hsame theta' zero' ∧
                  hsame graphLedger graphLedger' ∧ hsame endpointLedger endpointLedger' ∧
                    SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d)
                      (DeRhamBoundary d) hsame := by
  intro packet sameTheta' sameZero sameEta graphCont' endpointCont'
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet.left
  have boundaryTheta' : DeRhamBoundary d theta' := by
    cases boundaryRows.right.left with
    | intro preimage sameThetaPreimage =>
        exact Exists.intro preimage (hsame_trans sameTheta' sameThetaPreimage)
  have sameTheta'Zero' : hsame theta' zero' :=
    hsame_trans sameTheta' (hsame_trans boundaryRows.left sameZero)
  have sameGraph : hsame graphLedger graphLedger' :=
    cont_respects_hsame (hsame_symm sameTheta') sameZero
      packet.right.right.right.left graphCont'
  have sameEndpoint : hsame endpointLedger endpointLedger' :=
    cont_respects_hsame sameGraph sameEta packet.right.right.right.right endpointCont'
  have cert : SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d)
      (DeRhamBoundary d) hsame := {
    core := {
      carrier_inhabited := Exists.intro theta' boundaryTheta'
      equiv_refl := by
        intro h _boundaryH
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same boundaryH
        cases boundaryH with
        | intro preimage sameH =>
            exact Exists.intro preimage (hsame_trans (hsame_symm same) sameH)
    }
    pattern_sound := by
      intro _h boundaryH
      exact boundaryH
    ledger_sound := by
      intro _h boundaryH
      exact boundaryH
  }
  exact And.intro boundaryTheta'
    (And.intro sameTheta'Zero'
      (And.intro sameGraph (And.intro sameEndpoint cert)))

theorem DeRhamBoundarySourceLedgerPacket_bridge_classifier_source_scope_packet_rows
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
