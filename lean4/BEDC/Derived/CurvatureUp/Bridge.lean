import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureBracketCarrier_standard_bridge_boundary [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB boundary
      curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
          classifier bundle pkg ->
        UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
          hsame boundary (append derivativeA derivativeB) ∧
            hsame curvatureLedger (append boundary provenance0) ∧
              hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
                PkgSig bundle classifier pkg := by
  intro carrier envelope
  have boundaryRows := CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro boundaryRows.left
    (And.intro boundaryRows.right.left
      (And.intro boundaryRows.right.right.left
        (And.intro boundaryRows.right.right.right
          (And.intro envelope.right.right.right.right.right.right.right.left
            envelope.right.right.right.right.right.right.right.right))))

end BEDC.Derived.CurvatureUp
