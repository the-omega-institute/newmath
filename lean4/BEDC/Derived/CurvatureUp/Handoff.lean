import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CurvatureChernWeilHandoffPacket [AskSetup] [PackageSetup]
    (curvature derham provenance connectionLedger classifier handoff : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier
      bundle pkg ∧
    Cont classifier provenance handoff ∧ PkgSig bundle handoff pkg

theorem CurvatureChernWeilHandoffPacket_provenance_exactness [AskSetup] [PackageSetup]
    {curvature derham provenance connectionLedger classifier handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CurvatureChernWeilHandoffPacket curvature derham provenance connectionLedger classifier
        handoff bundle pkg ->
      CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier
          bundle pkg ∧
        UnaryHistory handoff ∧ hsame handoff (append classifier provenance) ∧
          PkgSig bundle handoff pkg := by
  intro packet
  have envelope :
      CurvatureChernWeilSourceEnvelope curvature derham provenance connectionLedger classifier
        bundle pkg :=
    packet.left
  have provenanceUnary : UnaryHistory provenance :=
    envelope.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    envelope.right.right.right.right.left
  have handoffCont : Cont classifier provenance handoff :=
    packet.right.left
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed classifierUnary provenanceUnary handoffCont
  exact And.intro envelope
    (And.intro handoffUnary (And.intro handoffCont packet.right.right))

end BEDC.Derived.CurvatureUp
