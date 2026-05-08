import BEDC.Derived.ConnectionUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

def CurvatureBracketCarrier
    (base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger : BHist) : Prop :=
  ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
    ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
      Cont derivativeA derivativeB boundary ∧ Cont boundary provenance curvatureLedger

theorem CurvatureBracketCarrier_boundary_rows
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeA derivativeB boundary ∧ Cont boundary provenance curvatureLedger := by
  intro carrier
  exact carrier.right.right

theorem CurvatureBracketCarrier_boundary_source_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA
      ledgerB boundary curvatureLedger ->
      UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
        hsame boundary (append derivativeA derivativeB) ∧
          hsame curvatureLedger (append boundary provenance) := by
  intro carrier
  have boundaryProjection :=
    ConnectionCarrierPacket_curvature_boundary_obligation carrier.left carrier.right.left
      carrier.right.right.left carrier.right.right.right
  exact And.intro boundaryProjection.left
    (And.intro boundaryProjection.right.left
      (And.intro boundaryProjection.right.right.left boundaryProjection.right.right.right.left))

end BEDC.Derived.CurvatureUp
