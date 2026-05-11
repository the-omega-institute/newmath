import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StatManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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
def StatManifoldPacket [AskSetup] [PackageSetup]
    (manifold fisher theta distribution metric primal dual provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory theta ∧
    UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory primal ∧
      UnaryHistory dual ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
        UnaryHistory endpoint ∧ hsame metric (append fisher distribution) ∧
          Cont (append (append manifold fisher) theta) ledger endpoint ∧
            PkgSig bundle endpoint pkg

theorem StatManifoldPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric primal dual provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldPacket manifold fisher theta distribution metric primal dual provenance ledger
      endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              StatManifoldPacket manifold fisher theta distribution metric primal dual provenance
                ledger e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              StatManifoldPacket manifold fisher theta distribution metric primal dual provenance
                ledger e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              StatManifoldPacket manifold fisher theta distribution metric primal dual provenance
                ledger e bundle pkg ∧ hsame row e)
          hsame ∧
        hsame metric (append fisher distribution) ∧
          Cont (append (append manifold fisher) theta) ledger endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint (Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          cases source with
          | intro e data =>
              exact Exists.intro e
                (And.intro data.left (hsame_trans (hsame_symm same) data.right))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · exact
      And.intro packet.right.right.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right.right.right.right)

end BEDC.Derived.StatManifoldUp
