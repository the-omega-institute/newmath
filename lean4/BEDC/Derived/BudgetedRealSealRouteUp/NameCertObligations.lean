import BEDC.Derived.BudgetedRealSealRouteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BudgetedRealSealRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BudgetedRealSealRouteCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {selector threshold observationBudget limitSeal realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle provenance pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row realSeal ∧
            budgetedRealSealRouteFields
              (BudgetedRealSealRouteUp.mk selector threshold observationBudget limitSeal
                realSeal transport replay provenance localName) =
              [selector, threshold, observationBudget, limitSeal, realSeal, transport, replay,
                provenance, localName])
        (fun row : BHist => hsame row realSeal)
        (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro provenancePkg
  have sourceRealSeal :
      (fun row : BHist =>
        hsame row realSeal ∧
          budgetedRealSealRouteFields
            (BudgetedRealSealRouteUp.mk selector threshold observationBudget limitSeal
              realSeal transport replay provenance localName) =
            [selector, threshold, observationBudget, limitSeal, realSeal, transport, replay,
              provenance, localName]) realSeal := by
    exact And.intro (hsame_refl realSeal) rfl
  exact {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceRealSeal
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
        intro row other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left provenancePkg
  }

end BEDC.Derived.BudgetedRealSealRouteUp
