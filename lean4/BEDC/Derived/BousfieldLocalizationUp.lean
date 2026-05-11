import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BousfieldLocalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BousfieldLocalizationFinitePacket [AskSetup] [PackageSetup]
    (model selected localObj classifier provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObj ∧
    UnaryHistory classifier ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
      Cont model selected classifier ∧ Cont selected localObj ledger ∧ PkgSig bundle ledger pkg

theorem BousfieldLocalizationFinitePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {model selected localObj classifier provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
              bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
              bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          BousfieldLocalizationFinitePacket model selected localObj classifier provenance ledger
              bundle pkg ∧ hsame row ledger)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro ledger ⟨packet, hsame_refl ledger⟩
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

end BEDC.Derived.BousfieldLocalizationUp
