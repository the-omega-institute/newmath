import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CurvatureUp_StdBridge [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB boundary
      curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
          classifier bundle pkg ->
        SemanticNameCert
            (fun e : BHist =>
              exists b : BHist,
                CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                  provenance0 ledgerA ledgerB b e)
            (fun e : BHist =>
              exists b : BHist,
                CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                  provenance0 ledgerA ledgerB b e)
            (fun e : BHist =>
              exists b : BHist,
                CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                  provenance0 ledgerA ledgerB b e)
            (fun left right : BHist =>
              (exists lb : BHist,
                CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                  provenance0 ledgerA ledgerB lb left) /\
              (exists rb : BHist,
                CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                  provenance0 ledgerA ledgerB rb right) /\
              hsame left right) ∧
          UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
            hsame boundary (append derivativeA derivativeB) ∧
              hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
                PkgSig bundle classifier pkg := by
  intro carrier envelope
  have cert :=
    CurvatureBracketCarrier_semantic_name_certificate carrier
  have bridgeRows :=
    CurvatureBracketCarrier_standard_bridge_boundary carrier envelope
  exact
    ⟨cert,
      bridgeRows.left,
      bridgeRows.right.left,
      bridgeRows.right.right.left,
      bridgeRows.right.right.right.right.left,
      bridgeRows.right.right.right.right.right⟩

end BEDC.Derived.CurvatureUp
