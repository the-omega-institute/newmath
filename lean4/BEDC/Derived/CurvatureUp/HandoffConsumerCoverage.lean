import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CurvatureChernWeilHandoffPacket_consumer_coverage [AskSetup] [PackageSetup]
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance0 ledgerA ledgerB
      boundary curvatureLedger derham provenance connectionLedger classifier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance0
        ledgerA ledgerB boundary curvatureLedger ->
      CurvatureChernWeilSourceEnvelope curvatureLedger derham provenance connectionLedger
        classifier bundle pkg ->
        UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧ UnaryHistory derham ∧
          UnaryHistory provenance ∧ UnaryHistory connectionLedger ∧ UnaryHistory classifier ∧
            Cont boundary provenance0 curvatureLedger ∧
              Cont curvatureLedger derham provenance ∧
                Cont provenance connectionLedger classifier ∧
                  hsame classifier (append (append curvatureLedger derham) connectionLedger) ∧
                    PkgSig bundle classifier pkg := by
  intro carrier envelope
  have carrierRows :=
    CurvatureBracketCarrier_boundary_source_obligation carrier
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro envelope.right.left
        (And.intro envelope.right.right.left
          (And.intro envelope.right.right.right.left
            (And.intro envelope.right.right.right.right.left
              (And.intro carrier.right.right.right
                (And.intro envelope.right.right.right.right.right.left
                  (And.intro envelope.right.right.right.right.right.right.left
                    (And.intro envelope.right.right.right.right.right.right.right.left
                      envelope.right.right.right.right.right.right.right.right)))))))))

end BEDC.Derived.CurvatureUp
