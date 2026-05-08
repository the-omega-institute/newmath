import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CurvatureBracketCarrier_ledger_exactness_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger swappedBoundary swappedCurvatureLedger pair cyclic : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeB derivativeA swappedBoundary ->
        Cont swappedBoundary provenance swappedCurvatureLedger ->
          Cont boundary swappedBoundary pair ->
            Cont pair boundary cyclic ->
              CurvatureBracketCarrier base fibre sec tangentB tangentA derivativeB derivativeA
                  provenance ledgerB ledgerA swappedBoundary swappedCurvatureLedger ∧
                UnaryHistory boundary ∧
                  UnaryHistory swappedBoundary ∧
                    UnaryHistory pair ∧
                      UnaryHistory cyclic ∧
                        hsame swappedCurvatureLedger (append swappedBoundary provenance) ∧
                          hsame cyclic (append (append boundary swappedBoundary) boundary) := by
  intro carrier swappedBoundaryCont swappedCurvatureCont pairCont cyclicCont
  have swappedRows :=
    CurvatureBracketCarrier_antisymmetric_bracket_obligation carrier swappedBoundaryCont
      swappedCurvatureCont
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  have swappedBoundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation swappedRows.left
  have pairUnary : UnaryHistory pair :=
    unary_cont_closed boundaryRows.left swappedBoundaryRows.left pairCont
  have cyclicUnary : UnaryHistory cyclic :=
    unary_cont_closed pairUnary boundaryRows.left cyclicCont
  have cyclicReadback : hsame cyclic (append (append boundary swappedBoundary) boundary) :=
    hsame_trans cyclicCont (congrArg (fun row : BHist => append row boundary) pairCont)
  exact And.intro swappedRows.left
    (And.intro boundaryRows.left
      (And.intro swappedBoundaryRows.left
        (And.intro pairUnary
          (And.intro cyclicUnary
            (And.intro swappedBoundaryRows.right.right.right cyclicReadback)))))

end BEDC.Derived.CurvatureUp
