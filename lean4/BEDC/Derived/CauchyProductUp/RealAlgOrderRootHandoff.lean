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

theorem CauchyProductPacket_realalgorder_root_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realAlgOrderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realAlgOrderRead ->
            PkgSig bundle realAlgOrderRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realAlgOrderRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row classifier ∨ hsame row budgetClassifier ∨
                      hsame row budgetSeal ∨ hsame row realAlgOrderRead ∨
                        Cont budgetSeal routes realAlgOrderRead)
                  (fun row : BHist =>
                    PkgSig bundle name pkg ∧ PkgSig bundle realAlgOrderRead pkg ∧
                      hsame row realAlgOrderRead)
                  hsame ∧
                UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                    UnaryHistory realAlgOrderRead ∧ Cont product ledger classifier ∧
                      Cont classifier routes budgetClassifier ∧
                        Cont budgetClassifier ledger budgetSeal ∧
                          Cont budgetSeal routes realAlgOrderRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle realAlgOrderRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierBudget budgetSealRoute realAlgOrderRoute realAlgOrderPkg
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
  have realAlgOrderReadUnary : UnaryHistory realAlgOrderRead :=
    unary_cont_closed budgetSealUnary routesUnary realAlgOrderRoute
  have sourceRead :
      (fun row : BHist => hsame row realAlgOrderRead ∧ UnaryHistory row)
        realAlgOrderRead := by
    exact ⟨hsame_refl realAlgOrderRead, realAlgOrderReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realAlgOrderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row classifier ∨ hsame row budgetClassifier ∨
              hsame row budgetSeal ∨ hsame row realAlgOrderRead ∨
                Cont budgetSeal routes realAlgOrderRead)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle realAlgOrderRead pkg ∧
              hsame row realAlgOrderRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realAlgOrderRead sourceRead
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨namePkg, realAlgOrderPkg, source.left⟩
    }
  exact
    ⟨cert, productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      realAlgOrderReadUnary, classifierRoute, classifierBudget, budgetSealRoute,
      realAlgOrderRoute, namePkg, realAlgOrderPkg⟩

end BEDC.Derived.CauchyProductUp
