import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DeRhamStandardBoundaryBridgePacket_input_source_scope
    {d : BHist -> BHist} {omega eta theta zero provenance bridge : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      exists graphLedger endpointLedger : BHist,
        DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ∧
          DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty ∧
            SemanticNameCert (fun h : BHist => hsame (d h) BHist.Empty)
              (fun h : BHist => hsame (d h) BHist.Empty)
              (fun h : BHist => hsame (d h) BHist.Empty) hsame ∧
                Cont provenance theta bridge := by
  intro packet
  have sourceRows :=
    DeRhamStandardBoundaryBridgePacket_source_exhaustion
      (d := d) (omega := omega) (eta := eta) (theta := theta) (zero := zero)
      (provenance := provenance) (bridge := bridge) packet
  have cocycleRows :=
    DeRhamDoubleExteriorPacket_cohomology_cocycle_readback
      (d := d) (omega := omega) (eta := eta) (theta := theta) (zero := zero) packet.left
  cases sourceRows with
  | intro graphLedger endpointRows =>
      cases endpointRows with
      | intro endpointLedger rows =>
          exact Exists.intro graphLedger
            (Exists.intro endpointLedger
              (And.intro rows.left
                (And.intro rows.right.left
                  (And.intro rows.right.right.left
                    (And.intro rows.right.right.right.left
                      (And.intro cocycleRows.right packet.right))))))

theorem DeRhamStandardBoundaryBridgePacket_bridge_classifier_source_scope
    {d : BHist -> BHist} {omega eta theta zero provenance bridge : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      let Source := fun row : BHist =>
        DeRhamBoundary d row ∧ hsame row zero ∧ hsame (d eta) BHist.Empty ∧
          Cont provenance row bridge
      SemanticNameCert Source Source Source
          (fun row other : BHist => Source row ∧ Source other ∧ hsame row other) ∧
        Source theta := by
  intro packet
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet.left
  have sourceTheta :
      DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty ∧
        Cont provenance theta bridge :=
    And.intro boundaryRows.right.left
      (And.intro boundaryRows.left (And.intro boundaryRows.right.right packet.right))
  let Source := fun row : BHist =>
    DeRhamBoundary d row ∧ hsame row zero ∧ hsame (d eta) BHist.Empty ∧
      Cont provenance row bridge
  have sourceTheta' : Source theta := sourceTheta
  have core :
      NameCert Source
        (fun row other : BHist => Source row ∧ Source other ∧ hsame row other) := {
    carrier_inhabited := Exists.intro theta sourceTheta'
    equiv_refl := by
      intro h sourceH
      exact And.intro sourceH (And.intro sourceH (hsame_refl h))
    equiv_symm := by
      intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    carrier_respects_equiv := by
      intro h k classified _sourceH
      exact classified.right.left
  }
  have cert :
      SemanticNameCert Source Source Source
        (fun row other : BHist => Source row ∧ Source other ∧ hsame row other) := {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert sourceTheta'

end BEDC.Derived.DeRhamUp
