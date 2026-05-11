import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StatManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StatManifoldCarrierPacket [AskSetup] [PackageSetup]
    (manifold fisher theta distribution metric connection dualConnection provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory theta ∧
    UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory connection ∧
      UnaryHistory dualConnection ∧ Cont manifold fisher ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem StatManifoldCarrierPacket_ledger_exactness [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric connection dualConnection provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldCarrierPacket manifold fisher theta distribution metric connection dualConnection
        provenance ledger endpoint bundle pkg ->
      UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory metric ∧
        UnaryHistory connection ∧ UnaryHistory dualConnection ∧ Cont manifold fisher ledger ∧
          hsame ledger (append manifold fisher) ∧ Cont provenance ledger endpoint ∧
            hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.right.left
                  (And.intro packet.right.right.right.right.right.right.right.right.left
                    packet.right.right.right.right.right.right.right.right.right))))))))

end BEDC.Derived.StatManifoldUp
