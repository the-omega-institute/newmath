import BEDC.Derived.StopCodonZeckendorfSuffixUp.TasteGate

namespace BEDC.Derived.StopCodonZeckendorfSuffixUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem StopCodonZeckendorfVisionRoute [AskSetup] [PackageSetup]
    {atlas window suffix legality bridge separation boundary transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont atlas window suffix → Cont suffix legality bridge → Cont separation boundary route →
      PkgSig bundle provenance pkg → PkgSig bundle name pkg →
        SemanticNameCert
          (fun row : BHist => hsame row name ∧ Cont suffix legality bridge ∧
            Cont separation boundary route)
          (fun row : BHist => hsame row suffix ∨ hsame row legality ∨ hsame row bridge ∨
            hsame row route ∨ hsame row name)
          (fun row : BHist => hsame row name ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _atlasWindow suffixLegality separationBoundary provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro name ⟨hsame_refl name, suffixLegality, separationBoundary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left, source.right.left,
            source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }

end BEDC.Derived.StopCodonZeckendorfSuffixUp
