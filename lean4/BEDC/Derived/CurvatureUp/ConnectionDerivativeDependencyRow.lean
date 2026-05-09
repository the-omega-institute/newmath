import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CurvatureBracketCarrier_connection_derivative_dependency_row
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      curvatureLedger : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeA derivativeB boundary ∧
        Cont boundary provenance curvatureLedger ∧
          hsame boundary (append derivativeA derivativeB) ∧
            hsame curvatureLedger (append boundary provenance) := by
  intro carrier
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro carrier.right.right.left
    (And.intro carrier.right.right.right
      (And.intro boundaryRows.right.right.left boundaryRows.right.right.right))

end BEDC.Derived.CurvatureUp
