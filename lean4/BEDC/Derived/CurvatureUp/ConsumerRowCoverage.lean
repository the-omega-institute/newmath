import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureBracketCarrier_consumer_row_coverage [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger consumerLedger consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      Cont curvatureLedger provenance consumerLedger ->
        Cont consumerLedger boundary consumerEndpoint ->
          PkgSig bundle consumerEndpoint pkg ->
            UnaryHistory consumerLedger ∧ UnaryHistory consumerEndpoint ∧
              hsame consumerLedger (append curvatureLedger provenance) ∧
                hsame consumerEndpoint (append (append curvatureLedger provenance) boundary) ∧
                  PkgSig bundle consumerEndpoint pkg := by
  intro carrier consumerLedgerCont consumerEndpointCont pkgSig
  have boundaryRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  have provenanceUnary : UnaryHistory provenance :=
    carrier.left.right.right.right.left
  have consumerLedgerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed boundaryRows.right.left provenanceUnary consumerLedgerCont
  have consumerEndpointUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed consumerLedgerUnary boundaryRows.left consumerEndpointCont
  have consumerEndpointReadback :
      hsame consumerEndpoint (append (append curvatureLedger provenance) boundary) :=
    hsame_trans consumerEndpointCont
      (congrArg (fun row : BHist => append row boundary) consumerLedgerCont)
  exact And.intro consumerLedgerUnary
    (And.intro consumerEndpointUnary
      (And.intro consumerLedgerCont
        (And.intro consumerEndpointReadback pkgSig)))

end BEDC.Derived.CurvatureUp
