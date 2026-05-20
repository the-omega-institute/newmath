import BEDC.Derived.CompactNetModulusBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CompactNetModulusBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CompactNetModulusBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compactNet modulus fold uniform selector transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle provenance pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row uniform ∧
            compactNetModulusBudgetFields
                (CompactNetModulusBudgetUp.mk compactNet modulus fold uniform selector
                  transport route provenance name) =
              [compactNet, modulus, fold, uniform, selector, transport, route,
                provenance, name])
        (fun row : BHist => hsame row uniform)
        (fun row : BHist => hsame row uniform ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame PkgSig
  intro provenancePkg
  exact {
    core := {
      carrier_inhabited := by
        exact Exists.intro uniform ⟨hsame_refl uniform, rfl⟩
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

end BEDC.Derived.CompactNetModulusBudgetUp
