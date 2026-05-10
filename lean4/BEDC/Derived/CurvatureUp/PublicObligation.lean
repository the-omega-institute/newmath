import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureBracketCarrier_public_obligation_surface
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger boundary' curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeA derivativeB boundary' ->
        Cont boundary' provenance curvatureLedger' ->
          ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ∧
            ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ∧
              hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' ∧
                UnaryHistory boundary ∧ UnaryHistory curvatureLedger := by
  intro carrier boundaryCont' curvatureCont'
  have sameRows :=
    CurvatureBracketCarrier_boundary_determinacy carrier boundaryCont' curvatureCont'
  have sourceRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro sameRows.left
        (And.intro sameRows.right
          (And.intro sourceRows.left sourceRows.right.left))))

end BEDC.Derived.CurvatureUp
