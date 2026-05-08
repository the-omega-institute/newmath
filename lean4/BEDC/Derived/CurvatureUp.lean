import BEDC.Derived.ConnectionUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

def CurvatureBoundaryPacket
    (base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist) : Prop :=
  ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
    ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
      Cont derivativeA derivativeB boundary ∧ Cont boundary provenance curvatureLedger

theorem CurvatureBoundaryPacket_boundary_source_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBoundaryPacket base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
        hsame boundary (append derivativeA derivativeB) ∧
          hsame curvatureLedger (append boundary provenance) ∧
            hsame curvatureLedger
              (append (append (append base fibre) tangentA)
                (append (append (append base fibre) tangentB) provenance)) := by
  intro packet
  exact ConnectionCarrierPacket_curvature_boundary_obligation packet.left packet.right.left
    packet.right.right.left packet.right.right.right

end BEDC.Derived.CurvatureUp
