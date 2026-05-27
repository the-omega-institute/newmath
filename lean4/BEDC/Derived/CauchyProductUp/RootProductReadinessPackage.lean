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

theorem CauchyProductPacket_root_product_readiness_package [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal readiness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes readiness ->
            PkgSig bundle readiness pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row product ∨ hsame row classifier ∨ hsame row budgetClassifier ∨
                      hsame row budgetSeal ∨ hsame row readiness)
                  (fun row : BHist =>
                    hsame row product ∨ hsame row classifier ∨ hsame row budgetClassifier ∨
                      hsame row budgetSeal ∨ hsame row readiness)
                  (fun row : BHist =>
                    PkgSig bundle readiness pkg ∧
                      (hsame row product ∨ hsame row classifier ∨
                        hsame row budgetClassifier ∨ hsame row budgetSeal ∨
                          hsame row readiness))
                  hsame ∧
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                  UnaryHistory budgetSeal ∧ UnaryHistory readiness ∧
                    Cont product ledger classifier ∧ Cont classifier routes budgetClassifier ∧
                      Cont budgetClassifier ledger budgetSeal ∧ Cont budgetSeal routes readiness ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle readiness pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierBudget budgetSealRoute readinessRoute readinessPkg
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
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed budgetSealUnary routesUnary readinessRoute
  have sourceAtReadiness :
      hsame readiness product ∨ hsame readiness classifier ∨
        hsame readiness budgetClassifier ∨ hsame readiness budgetSeal ∨
          hsame readiness readiness :=
    Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl readiness))))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row budgetClassifier ∨
              hsame row budgetSeal ∨ hsame row readiness)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row budgetClassifier ∨
              hsame row budgetSeal ∨ hsame row readiness)
          (fun row : BHist =>
            PkgSig bundle readiness pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row budgetClassifier ∨
                hsame row budgetSeal ∨ hsame row readiness))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readiness sourceAtReadiness
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
            | inr tail =>
                cases tail with
                | inl rowBudgetClassifier =>
                    exact Or.inr
                      (Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) rowBudgetClassifier)))
                | inr tail =>
                    cases tail with
                    | inl rowBudgetSeal =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) rowBudgetSeal))))
                    | inr rowReadiness =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm sameRows) rowReadiness))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro readinessPkg source
  }
  exact
    ⟨cert, productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      readinessUnary, classifierRoute, classifierBudget, budgetSealRoute, readinessRoute,
      namePkg, readinessPkg⟩

end BEDC.Derived.CauchyProductUp
