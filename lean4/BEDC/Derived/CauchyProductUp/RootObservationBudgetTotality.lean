import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_observation_budget_totality [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal observationBudget :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        UnaryHistory budgetSeal ->
        Cont budgetClassifier budgetSeal observationBudget ->
          PkgSig bundle observationBudget pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row observationBudget ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                    hsame row classifier ∨ hsame row observationBudget)
                (fun row : BHist =>
                  PkgSig bundle observationBudget pkg ∧ hsame row observationBudget)
                hsame ∧
              UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory budgetClassifier ∧ UnaryHistory observationBudget ∧
                  Cont product ledger classifier ∧ Cont classifier routes budgetClassifier ∧
                    Cont budgetClassifier budgetSeal observationBudget ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle observationBudget pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont hsame
  intro packet classifierBudget budgetSealUnary budgetObservation observationBudgetPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have observationBudgetUnary : UnaryHistory observationBudget :=
    unary_cont_closed budgetClassifierUnary budgetSealUnary budgetObservation
  have sourceAtObservationBudget :
      hsame observationBudget observationBudget ∧ UnaryHistory observationBudget :=
    And.intro (hsame_refl observationBudget) observationBudgetUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row observationBudget ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row classifier ∨ hsame row observationBudget)
          (fun row : BHist =>
            PkgSig bundle observationBudget pkg ∧ hsame row observationBudget)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro observationBudget sourceAtObservationBudget
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
        intro _row other sameRows source
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact And.intro observationBudgetPkg source.left
  }
  exact
    ⟨cert, productUnary, classifierUnary, budgetClassifierUnary, observationBudgetUnary,
      classifierRoute, classifierBudget, budgetObservation, namePkg, observationBudgetPkg⟩

end BEDC.Derived.CauchyProductUp
