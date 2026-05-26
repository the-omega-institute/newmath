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

theorem CauchyProductPacket_regseqrat_product_budget_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
            PkgSig bundle budgetSeal pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row product ∨ hsame row classifier ∨ hsame row budgetSeal)
                (fun row : BHist =>
                  hsame row product ∨ hsame row classifier ∨ hsame row budgetSeal)
                (fun row : BHist =>
                  PkgSig bundle budgetSeal pkg ∧
                    (hsame row product ∨ hsame row classifier ∨ hsame row budgetSeal))
                hsame ∧
              UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont classifier routes budgetClassifier ∧
                      Cont budgetClassifier ledger budgetSeal ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierBudget budgetSealRoute budgetSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have sourceAtClassifier :
      hsame classifier product ∨ hsame classifier classifier ∨ hsame classifier budgetSeal :=
    Or.inr (Or.inl (hsame_refl classifier))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row budgetSeal)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row budgetSeal)
          (fun row : BHist =>
            PkgSig bundle budgetSeal pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row budgetSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifier sourceAtClassifier
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
        cases source with
        | inl rowProduct =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowProduct)
        | inr tail =>
            cases tail with
            | inl rowClassifier =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowClassifier))
            | inr rowBudgetSeal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowBudgetSeal))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro budgetSealPkg source
  }
  exact
    ⟨cert, productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      productRoute, classifierRoute, classifierBudget, budgetSealRoute, namePkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
