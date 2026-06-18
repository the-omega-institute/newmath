import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Derived.RegularCauchyProductBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RegularCauchyProductBudget_namecert_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB dyadicA dyadicB product budget readback sealRow
      transport routes provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont windowA windowB product ->
      Cont product budget readback ->
        Cont readback sealRow publicRead ->
          PkgSig bundle provenance pkg ->
            PkgSig bundle name pkg ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead)
                    (fun row : BHist =>
                      hsame row product ∨ hsame row budget ∨ hsame row readback ∨
                        hsame row sealRow ∨ hsame row publicRead)
                    (fun row : BHist =>
                      hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  Cont windowA windowB product ∧ Cont product budget readback ∧
                    Cont readback sealRow publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro windowProductRoute productBudgetRoute sealRoute provenancePkg namePkg publicPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist =>
            hsame row product ∨ hsame row budget ∨ hsame row readback ∨
              hsame row sealRow ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead (hsame_refl publicRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source)))
    ledger_sound := by
      intro _row source
      exact ⟨source, publicPkg⟩
  }
  exact
    ⟨cert, windowProductRoute, productBudgetRoute, sealRoute, provenancePkg, namePkg,
      publicPkg⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
