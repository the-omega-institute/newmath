import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CurvatureChernWeilConsumerRow [AskSetup] [PackageSetup]
    (curvature derham provenance connectionLedger classRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classRow bundle pkg

theorem CurvatureChernWeilConsumerRow_source_envelope_projection [AskSetup] [PackageSetup]
    {curvature derham provenance connectionLedger classRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilConsumerRow curvature derham provenance connectionLedger classRow
        bundle pkg ->
      UnaryHistory curvature ∧ UnaryHistory derham ∧ UnaryHistory provenance ∧
        UnaryHistory connectionLedger ∧ UnaryHistory classRow ∧
          Cont curvature derham provenance ∧ Cont provenance connectionLedger classRow ∧
            hsame classRow (append (append curvature derham) connectionLedger) ∧
              PkgSig bundle classRow pkg := by
  intro row
  exact row

end BEDC.Derived.CurvatureUp
