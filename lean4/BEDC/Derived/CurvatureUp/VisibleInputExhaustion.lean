import BEDC.Derived.CurvatureUp.ConsumerBoundary
import BEDC.Derived.CurvatureUp.SourceEnvelopeProjection

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.Derived.ConnectionUp

theorem CurvatureChernWeilSourceEnvelope_visible_input_exhaustion [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB boundary
      curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
          classifier bundle pkg ->
        ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance0 ledgerA ∧
          ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance0 ledgerB ∧
            Cont derivativeA derivativeB boundary ∧
              Cont boundary provenance0 curvatureLedger ∧
                Cont curvatureLedger derham provenance ∧
                  Cont provenance connectionLedger classifier ∧
                    hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
                      PkgSig bundle classifier pkg := by
  intro carrier envelope
  have carrierRows :=
    CurvatureBracketCarrier_source_row_coverage carrier
  have envelopeRows :=
    CurvatureChernWeilSourceEnvelope_source_envelope_projection carrier envelope
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro carrierRows.right.right.left
        (And.intro carrierRows.right.right.right.left
          (And.intro envelopeRows.right.right.right.right.right.left
            (And.intro envelopeRows.right.right.right.right.right.right.left
              (And.intro envelopeRows.right.right.right.right.right.right.right.left
                envelopeRows.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.CurvatureUp
