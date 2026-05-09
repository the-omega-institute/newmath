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

end BEDC.Derived.DeRhamUp
