import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream directed modulus endpoint compat transport consumer provenance name row : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory compat ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        UnaryHistory row ∧ Cont stream directed transport ∧
          Cont modulus endpoint compat ∧ Cont compat transport row ∧
            Cont row consumer provenance ∧ PkgSig bundle provenance pkg

theorem CauchyFilterPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {stream directed modulus endpoint compat transport consumer provenance name row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream directed modulus endpoint compat transport consumer provenance
        name row bundle pkg ->
      SemanticNameCert
        (fun q : BHist =>
          CauchyFilterPacket stream directed modulus endpoint compat transport consumer provenance
              name row bundle pkg ∧ hsame q transport)
        (fun q : BHist =>
          CauchyFilterPacket stream directed modulus endpoint compat transport consumer provenance
              name row bundle pkg ∧ hsame q transport)
        (fun q : BHist =>
          CauchyFilterPacket stream directed modulus endpoint compat transport consumer provenance
              name row bundle pkg ∧ hsame q transport)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro transport ⟨packet, hsame_refl transport⟩
      equiv_refl := by
        intro q _carrier
        exact hsame_refl q
      equiv_symm := by
        intro q q' same
        exact hsame_symm same
      equiv_trans := by
        intro q q' q'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro q q' same carrier
        exact ⟨carrier.left, hsame_trans (hsame_symm same) carrier.right⟩
    }
    pattern_sound := by
      intro _q source
      exact source
    ledger_sound := by
      intro _q source
      exact source
  }

end BEDC.Derived.CauchyFilterUp
