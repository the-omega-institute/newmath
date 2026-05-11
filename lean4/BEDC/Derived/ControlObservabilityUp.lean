import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlObservabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ControlObservabilityCarrierPacket [AskSetup] [PackageSetup]
    (dynSystem matrix vecspace linmap state transition output observationStack traceLedger
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dynSystem ∧ UnaryHistory matrix ∧ UnaryHistory vecspace ∧
    UnaryHistory linmap ∧ UnaryHistory state ∧ Cont transition output observationStack ∧
      Cont observationStack provenance traceLedger ∧ Cont traceLedger provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem ControlObservabilityCarrierPacket_obligation_surface [AskSetup] [PackageSetup]
    {dynSystem matrix vecspace linmap state transition output observationStack traceLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityCarrierPacket dynSystem matrix vecspace linmap state transition output
        observationStack traceLedger provenance endpoint bundle pkg ->
      UnaryHistory dynSystem ∧ UnaryHistory matrix ∧ UnaryHistory vecspace ∧
        UnaryHistory linmap ∧ Cont transition output observationStack ∧
          Cont observationStack provenance traceLedger ∧
            Cont traceLedger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.left
                packet.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.ControlObservabilityUp
