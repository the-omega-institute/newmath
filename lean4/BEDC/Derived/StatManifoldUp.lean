import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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
