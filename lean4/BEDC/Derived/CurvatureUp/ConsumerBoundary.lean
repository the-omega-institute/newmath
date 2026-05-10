import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.ConnectionUp

theorem CurvatureChernWeilSourceEnvelope_consumer_boundary [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB
      boundary curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
          classifier bundle pkg ->
        ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance0 ledgerA ∧
          ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance0 ledgerB ∧
            UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧ UnaryHistory derham ∧
              UnaryHistory classifier ∧ Cont curvatureLedger derham provenance ∧
                Cont provenance connectionLedger classifier ∧ PkgSig bundle classifier pkg := by
  intro carrier envelope
  have carrierRows := CurvatureBracketCarrier_source_row_coverage carrier
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro carrierRows.right.right.right.right.left
        (And.intro carrierRows.right.right.right.right.right.left
          (And.intro envelope.right.left
            (And.intro envelope.right.right.right.right.left
              (And.intro envelope.right.right.right.right.right.left
                (And.intro envelope.right.right.right.right.right.right.left
                  envelope.right.right.right.right.right.right.right.right)))))))

end BEDC.Derived.CurvatureUp
