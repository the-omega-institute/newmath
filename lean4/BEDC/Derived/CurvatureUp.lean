import BEDC.Derived.ConnectionUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.ConnectionUp

theorem CurvatureBoundarySource_connection_projection
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ->
      ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ->
        Cont derivativeA derivativeB boundary ->
          Cont boundary provenance curvatureLedger ->
            hsame ledgerA (append (append (append base fibre) tangentA) provenance) ∧
              hsame ledgerB (append (append (append base fibre) tangentB) provenance) ∧
                hsame boundary (append derivativeA derivativeB) ∧
                  hsame curvatureLedger (append boundary provenance) := by
  intro packetA packetB boundaryCont curvatureCont
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetA
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetB
  have boundaryRows :=
    ConnectionCarrierPacket_curvature_boundary_obligation packetA packetB boundaryCont curvatureCont
  exact And.intro exactA.right.right.right.right.right
    (And.intro exactB.right.right.right.right.right
      (And.intro boundaryRows.right.right.left boundaryRows.right.right.right.left))

end BEDC.Derived.CurvatureUp
