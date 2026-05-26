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

theorem CauchyProductPacket_real_seal_multiplication_nonescape [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal
      multiplicationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            Cont realSeal routes multiplicationRead ->
              PkgSig bundle multiplicationRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                        hsame row multiplicationRead)
                    (fun row : BHist =>
                      hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                        hsame row multiplicationRead)
                    (fun row : BHist =>
                      PkgSig bundle multiplicationRead pkg ∧
                        (hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                          hsame row multiplicationRead))
                    hsame ∧
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory realSeal ∧ UnaryHistory multiplicationRead ∧
                        Cont product ledger classifier ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              Cont budgetSeal routes realSeal ∧
                                Cont realSeal routes multiplicationRead ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle multiplicationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute multiplicationRoute
    multiplicationPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _transportRoute, productRoute, classifierRoute, namePkg⟩ := packet
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
  have multiplicationReadUnary : UnaryHistory multiplicationRead :=
    unary_cont_closed realSealUnary routesUnary multiplicationRoute
  have sourceAtMultiplication :
      hsame multiplicationRead product ∨ hsame multiplicationRead classifier ∨
        hsame multiplicationRead realSeal ∨ hsame multiplicationRead multiplicationRead :=
    Or.inr (Or.inr (Or.inr (hsame_refl multiplicationRead)))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
              hsame row multiplicationRead)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
              hsame row multiplicationRead)
          (fun row : BHist =>
            PkgSig bundle multiplicationRead pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                hsame row multiplicationRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro multiplicationRead sourceAtMultiplication
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
                | inl rowRealSeal =>
                    exact Or.inr (Or.inr (Or.inl
                      (hsame_trans (hsame_symm sameRows) rowRealSeal)))
                | inr rowMultiplication =>
                    exact Or.inr (Or.inr (Or.inr
                      (hsame_trans (hsame_symm sameRows) rowMultiplication)))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro multiplicationPkg source
  }
  exact
    ⟨cert, productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      realSealUnary, multiplicationReadUnary, classifierRoute, classifierBudget,
      budgetSealRoute, realSealRoute, multiplicationRoute, namePkg, multiplicationPkg⟩

end BEDC.Derived.CauchyProductUp
