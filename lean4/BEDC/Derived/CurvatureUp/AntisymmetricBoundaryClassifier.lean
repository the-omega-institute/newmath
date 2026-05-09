import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Sig

theorem CurvatureBracketCarrier_antisymmetric_boundary_classifier [AskSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB boundary
      swappedBoundary curvatureLedger swappedCurvatureLedger orientation : BHist}
    {bundle : ProbeBundle ProbeName} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont derivativeB derivativeA swappedBoundary ->
        Cont swappedBoundary provenance swappedCurvatureLedger ->
          SigRel bundle boundary orientation ->
            CurvatureBracketCarrier base fibre sec tangentB tangentA derivativeB derivativeA
                provenance ledgerB ledgerA swappedBoundary swappedCurvatureLedger ∧
              hsame boundary swappedBoundary ∧
                hsame curvatureLedger swappedCurvatureLedger ∧ SigRel bundle boundary orientation := by
  intro carrier swappedBoundaryCont swappedCurvatureCont orientationRel
  have swappedRows :=
    CurvatureBracketCarrier_antisymmetric_bracket_obligation carrier swappedBoundaryCont
      swappedCurvatureCont
  exact And.intro swappedRows.left
    (And.intro swappedRows.right.left
      (And.intro swappedRows.right.right orientationRel))

end BEDC.Derived.CurvatureUp
