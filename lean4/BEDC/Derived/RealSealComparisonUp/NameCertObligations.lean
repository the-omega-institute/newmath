import BEDC.Derived.RealSealComparisonUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealSealComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealSealComparisonCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {seal0 seal1 uniqueness diagonal0 diagonal1 verdict transport continuation provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle provenance pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row verdict ∧
            realSealComparisonFields
                (RealSealComparisonUp.mk seal0 seal1 uniqueness diagonal0 diagonal1 verdict
                  transport continuation provenance nameCert) =
              [seal0, seal1, uniqueness, diagonal0, diagonal1, verdict, transport,
                continuation, provenance, nameCert])
        (fun row : BHist => hsame row verdict)
        (fun row : BHist => hsame row verdict ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame PkgSig
  intro provenancePkg
  exact {
    core := {
      carrier_inhabited := by
        exact Exists.intro verdict ⟨hsame_refl verdict, rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }

end BEDC.Derived.RealSealComparisonUp
