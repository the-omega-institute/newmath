import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyIntegralFormulaUp [AskSetup] [PackageSetup]
    (domain point contour socket series exclusion goursat formula transport provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont hsame UnaryHistory
  UnaryHistory domain ∧ UnaryHistory point ∧ UnaryHistory contour ∧
    UnaryHistory socket ∧ UnaryHistory series ∧ UnaryHistory exclusion ∧
      UnaryHistory goursat ∧ UnaryHistory formula ∧ UnaryHistory transport ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont domain point contour ∧ Cont contour socket series ∧
            Cont series exclusion goursat ∧ Cont goursat formula transport ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace CauchyIntegralFormulaUp

theorem CauchyIntegralFormulaCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {domain point contour socket series exclusion goursat formula transport provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.CauchyIntegralFormulaUp domain point contour socket series exclusion
        goursat formula transport provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BEDC.Derived.CauchyIntegralFormulaUp domain point contour socket series exclusion
              goursat formula transport provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.CauchyIntegralFormulaUp domain point contour socket series exclusion
              goursat formula transport provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.CauchyIntegralFormulaUp domain point contour socket series exclusion
              goursat formula transport provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrier, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end CauchyIntegralFormulaUp
end BEDC.Derived
