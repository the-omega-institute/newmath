import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CurvatureBracketCarrier_exactness_predicate_surface
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary boundary' curvatureLedger curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
          ledgerA ledgerB boundary' curvatureLedger' ->
        Cont derivativeA derivativeB boundary ∧ Cont derivativeA derivativeB boundary' ∧
          Cont boundary provenance curvatureLedger ∧
            Cont boundary' provenance curvatureLedger' ∧
              hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' ∧
                UnaryHistory boundary ∧ UnaryHistory curvatureLedger := by
  intro carrier carrier'
  have deterministic :=
    CurvatureBracketCarrier_boundary_row_determinacy carrier carrier'
  have sourceRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  exact
    ⟨deterministic.left,
      deterministic.right.left,
      deterministic.right.right.left,
      deterministic.right.right.right.left,
      deterministic.right.right.right.right.left,
      deterministic.right.right.right.right.right,
      sourceRows.left,
      sourceRows.right.left⟩

end BEDC.Derived.CurvatureUp
