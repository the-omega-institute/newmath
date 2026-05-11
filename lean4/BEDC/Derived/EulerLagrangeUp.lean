import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EulerLagrangeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EulerLagrangePacket [AskSetup] [PackageSetup]
    (action variation firstVariation boundary pde scalar route transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory action ∧ UnaryHistory variation ∧ UnaryHistory firstVariation ∧
    UnaryHistory boundary ∧ UnaryHistory pde ∧ UnaryHistory scalar ∧ UnaryHistory route ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont action variation firstVariation ∧ Cont firstVariation boundary pde ∧
          Cont pde scalar route ∧ Cont route transport name ∧ PkgSig bundle name pkg

theorem EulerLagrangePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {action variation firstVariation boundary pde scalar route transport provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
              provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
              provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
              provenance name bundle pkg ∧ hsame row name)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro name ⟨packet, hsame_refl name⟩
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

end BEDC.Derived.EulerLagrangeUp
