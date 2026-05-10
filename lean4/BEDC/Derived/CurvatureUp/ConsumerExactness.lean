import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureChernWeilSourceEnvelope_consumer_exactness [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB
      boundary curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
          classifier bundle pkg ->
        CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
            classifier bundle pkg ∧
          hsame curvatureLedger (append boundary provenance0) ∧
            hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
              PkgSig bundle classifier pkg := by
  intro carrier envelope
  have boundaryRows := CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro envelope
    (And.intro boundaryRows.right.right.right
      (And.intro envelope.right.right.right.right.right.right.right.left
        envelope.right.right.right.right.right.right.right.right))

end BEDC.Derived.CurvatureUp
