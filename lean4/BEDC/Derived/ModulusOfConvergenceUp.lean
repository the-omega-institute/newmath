import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergencePacket [AskSetup] [PackageSetup]
    (precision threshold requestWindow modulus schedule witnessWindow witness exportWindow ledger
      provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      Cont precision threshold requestWindow ∧ Cont modulus schedule witnessWindow ∧
        Cont requestWindow witness exportWindow ∧ Cont exportWindow ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision threshold requestWindow modulus schedule witnessWindow witness exportWindow ledger
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergencePacket precision threshold requestWindow modulus schedule witnessWindow
        witness exportWindow ledger provenance bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame ∧
        Cont precision threshold requestWindow ∧ Cont modulus schedule witnessWindow ∧
          Cont requestWindow witness exportWindow ∧ Cont exportWindow ledger provenance ∧
            PkgSig bundle provenance pkg := by
  intro packet
  have requestRow : Cont precision threshold requestWindow :=
    packet.right.right.right.right.right.right.left
  have witnessRow : Cont modulus schedule witnessWindow :=
    packet.right.right.right.right.right.right.right.left
  have exportRow : Cont requestWindow witness exportWindow :=
    packet.right.right.right.right.right.right.right.right.left
  have provenanceRow : Cont exportWindow ledger provenance :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro requestRow
      (And.intro witnessRow
        (And.intro exportRow
          (And.intro provenanceRow pkgSig))))

end BEDC.Derived.ModulusOfConvergenceUp
