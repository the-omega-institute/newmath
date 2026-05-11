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

def StatManifoldBHistPacket [AskSetup] [PackageSetup]
    (manifold fisher parameter distribution metric primalConnection dualConnection provenance
      ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory parameter ∧
    UnaryHistory distribution ∧ UnaryHistory primalConnection ∧ UnaryHistory provenance ∧
      Cont fisher parameter metric ∧ Cont metric primalConnection dualConnection ∧
        Cont provenance dualConnection ledger ∧ Cont ledger manifold endpoint ∧
          PkgSig bundle endpoint pkg

theorem StatManifoldBHistPacket_ledger_exactness [AskSetup] [PackageSetup]
    {manifold fisher parameter distribution metric primalConnection dualConnection provenance
      ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldBHistPacket manifold fisher parameter distribution metric primalConnection
        dualConnection provenance ledger endpoint bundle pkg ->
      hsame metric (append fisher parameter) ∧
        hsame dualConnection (append metric primalConnection) ∧
          hsame ledger (append provenance dualConnection) ∧
            hsame endpoint (append ledger manifold) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have metricRow : Cont fisher parameter metric :=
    packet.right.right.right.right.right.right.left
  have dualConnectionRow : Cont metric primalConnection dualConnection :=
    packet.right.right.right.right.right.right.right.left
  have ledgerRow : Cont provenance dualConnection ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont ledger manifold endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  exact And.intro metricRow
    (And.intro dualConnectionRow
      (And.intro ledgerRow
        (And.intro endpointRow
          packet.right.right.right.right.right.right.right.right.right.right)))

end BEDC.Derived.StatManifoldUp
