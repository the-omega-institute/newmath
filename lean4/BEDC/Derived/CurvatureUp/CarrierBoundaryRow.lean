import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CurvatureBracketCarrier_carrier_boundary_row
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger boundary' curvatureLedger' : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeA derivativeB boundary' ->
        Cont boundary' provenance curvatureLedger' ->
          CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
              ledgerA ledgerB boundary' curvatureLedger' ∧
            hsame boundary boundary' ∧ hsame curvatureLedger curvatureLedger' ∧
              UnaryHistory boundary' ∧ UnaryHistory curvatureLedger' := by
  intro carrier boundaryCont' curvatureCont'
  have carrier' :
      CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary' curvatureLedger' :=
    And.intro carrier.left
      (And.intro carrier.right.left (And.intro boundaryCont' curvatureCont'))
  have determinacy :=
    CurvatureBracketCarrier_boundary_determinacy carrier boundaryCont' curvatureCont'
  have sourceRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier'
  exact And.intro carrier'
    (And.intro determinacy.left
      (And.intro determinacy.right
        (And.intro sourceRows.left sourceRows.right.left)))

end BEDC.Derived.CurvatureUp
