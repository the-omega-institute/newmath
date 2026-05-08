import BEDC.Derived.ConnectionUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureCarrierPacket_connection_boundary_source_projection
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ->
      ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ->
        Cont derivativeA derivativeB boundary ->
          Cont boundary provenance curvatureLedger ->
            UnaryHistory base ∧ UnaryHistory fibre ∧ UnaryHistory sec ∧
              UnaryHistory tangentA ∧ UnaryHistory tangentB ∧ UnaryHistory derivativeA ∧
                UnaryHistory derivativeB ∧ UnaryHistory boundary ∧
                  UnaryHistory curvatureLedger ∧
                    hsame curvatureLedger
                      (append (append (append base fibre) tangentA)
                        (append (append (append base fibre) tangentB) provenance)) := by
  intro packetA packetB boundaryCont curvatureCont
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetA
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetB
  have boundary :=
    ConnectionCarrierPacket_curvature_boundary_obligation packetA packetB boundaryCont curvatureCont
  exact And.intro packetA.left
    (And.intro packetA.right.left
      (And.intro exactA.left
        (And.intro packetA.right.right.left
          (And.intro packetB.right.right.left
            (And.intro exactA.right.left
              (And.intro exactB.right.left
                (And.intro boundary.left
                  (And.intro boundary.right.left boundary.right.right.right.right))))))))

end BEDC.Derived.CurvatureUp
