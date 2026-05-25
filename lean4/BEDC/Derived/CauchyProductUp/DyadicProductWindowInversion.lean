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

theorem CauchyProductPacket_selector_product_seal_window_obligations
    [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorWindow selectorDyadic selectorRegular
      productSeal : BHist}
    {bundle selectorBundle : ProbeBundle ProbeName} {pkg selectorPkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont selectorWindow selectorDyadic selectorRegular ->
        Cont product selectorRegular productSeal ->
          PkgSig selectorBundle selectorRegular selectorPkg ->
            UnaryHistory selectorWindow ->
              UnaryHistory selectorDyadic ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
                  UnaryHistory observationB ∧ UnaryHistory product ∧
                    UnaryHistory selectorRegular ∧ UnaryHistory productSeal ∧
                      Cont observationA observationB product ∧
                        Cont selectorWindow selectorDyadic selectorRegular ∧
                          Cont product selectorRegular productSeal ∧ PkgSig bundle name pkg ∧
                            PkgSig selectorBundle selectorRegular selectorPkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet selectorRegularRoute productSealRoute selectorRegularPkg selectorWindowUnary
    selectorDyadicUnary
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have selectorRegularUnary : UnaryHistory selectorRegular :=
    unary_cont_closed selectorWindowUnary selectorDyadicUnary selectorRegularRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed productUnary selectorRegularUnary productSealRoute
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      selectorRegularUnary, productSealUnary, productRoute, selectorRegularRoute,
      productSealRoute, namePkg, selectorRegularPkg⟩

theorem CauchyProductPacket_dyadic_product_window_inversion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            PkgSig bundle realSeal pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                      hsame row budgetSeal ∨ hsame row realSeal)
                  (fun row : BHist =>
                    hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                      hsame row budgetSeal ∨ hsame row realSeal)
                  (fun row : BHist =>
                    PkgSig bundle realSeal pkg ∧
                      (hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                        hsame row budgetSeal ∨ hsame row realSeal))
                  hsame ∧
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory radiusA ∧
                  UnaryHistory radiusB ∧ UnaryHistory observationA ∧
                    UnaryHistory observationB ∧ UnaryHistory product ∧
                      UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                        UnaryHistory budgetSeal ∧ UnaryHistory realSeal ∧
                          Cont windowA windowB transport ∧
                            Cont observationA observationB product ∧
                              Cont product ledger classifier ∧
                                Cont classifier routes budgetClassifier ∧
                                  Cont budgetClassifier ledger budgetSeal ∧
                                    Cont budgetSeal routes realSeal ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierBudget budgetSealRoute realSealRoute realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
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
  have sourceAtRealSeal :
      (fun row : BHist =>
        hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
          hsame row budgetSeal ∨ hsame row realSeal) realSeal := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl realSeal))))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row budgetSeal ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
              hsame row budgetSeal ∨ hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row windowA ∨ hsame row windowB ∨ hsame row product ∨
                hsame row budgetSeal ∨ hsame row realSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtRealSeal
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
        | inl rowWindowA =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowWindowA)
        | inr tail =>
            cases tail with
            | inl rowWindowB =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindowB))
            | inr tail =>
                cases tail with
                | inl rowProduct =>
                    exact
                      Or.inr (Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) rowProduct)))
                | inr tail =>
                    cases tail with
                    | inl rowBudgetSeal =>
                        exact
                          Or.inr (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) rowBudgetSeal))))
                    | inr rowRealSeal =>
                        exact
                          Or.inr (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm sameRows) rowRealSeal))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary, observationAUnary,
      observationBUnary, productUnary, classifierUnary, budgetClassifierUnary,
      budgetSealUnary, realSealUnary, windowTransport, productRoute, classifierRoute,
      classifierBudget, budgetSealRoute, realSealRoute, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
