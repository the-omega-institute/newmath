import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_limitseal_selector_coherence [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal siblingSeal
      selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes budgetClassifier →
        Cont budgetClassifier ledger budgetSeal →
          Cont budgetSeal routes realSeal →
            Cont budgetSeal ledger siblingSeal →
              Cont realSeal routes selectorRead →
                Cont siblingSeal ledger selectorRead →
                  PkgSig bundle realSeal pkg →
                    PkgSig bundle siblingSeal pkg →
                      PkgSig bundle selectorRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row budgetSeal ∨ hsame row siblingSeal ∨
                                hsame row selectorRead)
                            (fun row : BHist =>
                              hsame row budgetSeal ∨ hsame row siblingSeal ∨
                                hsame row selectorRead)
                            (fun row : BHist =>
                              PkgSig bundle selectorRead pkg ∧
                                (hsame row budgetSeal ∨ hsame row siblingSeal ∨
                                  hsame row selectorRead))
                            hsame ∧
                          UnaryHistory budgetSeal ∧ UnaryHistory realSeal ∧
                            UnaryHistory siblingSeal ∧ UnaryHistory selectorRead ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierBudget budgetSealRoute realSealRoute siblingSealRoute
    selectorFromReal _selectorFromSibling realSealPkg siblingSealPkg selectorPkg
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
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary realSealRoute
  have siblingSealUnary : UnaryHistory siblingSeal :=
    unary_cont_closed budgetSealUnary ledgerUnary siblingSealRoute
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed realSealUnary routesUnary selectorFromReal
  have sourceAtBudgetSeal :
      hsame budgetSeal budgetSeal ∨ hsame budgetSeal siblingSeal ∨
        hsame budgetSeal selectorRead :=
    Or.inl (hsame_refl budgetSeal)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row budgetSeal ∨ hsame row siblingSeal ∨ hsame row selectorRead)
          (fun row : BHist =>
            hsame row budgetSeal ∨ hsame row siblingSeal ∨ hsame row selectorRead)
          (fun row : BHist =>
            PkgSig bundle selectorRead pkg ∧
              (hsame row budgetSeal ∨ hsame row siblingSeal ∨ hsame row selectorRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetSeal sourceAtBudgetSeal
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
        | inl rowBudgetSeal =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowBudgetSeal)
        | inr tail =>
            cases tail with
            | inl rowSiblingSeal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowSiblingSeal))
            | inr rowSelectorRead =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowSelectorRead))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro selectorPkg source
  }
  exact
    ⟨cert, budgetSealUnary, realSealUnary, siblingSealUnary, selectorReadUnary, namePkg,
      selectorPkg⟩

end BEDC.Derived.CauchyProductUp
