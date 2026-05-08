import BEDC.Derived.ConnectionUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.CurvatureUp

open BEDC.Derived.ConnectionUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.CurvatureUp
