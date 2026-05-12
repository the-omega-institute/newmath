import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BitVectorSourcePacket [AskSetup] [PackageSetup]
    (length spine ledger provenance route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧
    UnaryHistory provenance ∧ UnaryHistory route ∧ UnaryHistory endpoint ∧
      Cont length spine route ∧ Cont route ledger endpoint ∧
        Cont endpoint provenance provenance ∧ PkgSig bundle endpoint pkg

theorem BitVectorSourcePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {length spine ledger provenance route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorSourcePacket length spine ledger provenance route endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BitVectorSourcePacket length spine ledger provenance route endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          BitVectorSourcePacket length spine ledger provenance route endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          BitVectorSourcePacket length spine ledger provenance route endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨packet, hsame_refl endpoint⟩
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same carrier
        exact ⟨carrier.left, hsame_trans (hsame_symm same) carrier.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.BitVectorUp
