import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_real_seal_compatibility [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetWindow budgetDyadic budgetRegSeq budgetSeal
      budgetConsumer realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory budgetWindow ->
        UnaryHistory budgetDyadic ->
          UnaryHistory budgetSeal ->
            Cont classifier routes realSeal ->
              Cont budgetWindow budgetDyadic budgetRegSeq ->
                Cont budgetRegSeq budgetSeal budgetConsumer ->
                  PkgSig bundle budgetConsumer pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row classifier ∨ hsame row budgetRegSeq ∨
                          hsame row budgetConsumer ∨ hsame row realSeal)
                      (fun row : BHist =>
                        hsame row classifier ∨ hsame row budgetRegSeq ∨
                          hsame row budgetConsumer ∨ Cont classifier routes realSeal)
                      (fun row : BHist =>
                        PkgSig bundle budgetConsumer pkg ∧
                          (hsame row classifier ∨ hsame row budgetRegSeq ∨
                            hsame row budgetConsumer ∨ hsame row realSeal))
                      hsame ∧
                      UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                        UnaryHistory budgetRegSeq ∧ UnaryHistory budgetConsumer ∧
                          Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                            Cont budgetWindow budgetDyadic budgetRegSeq ∧
                              Cont budgetRegSeq budgetSeal budgetConsumer ∧
                                PkgSig bundle name pkg ∧
                                  PkgSig bundle budgetConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet budgetWindowUnary budgetDyadicUnary budgetSealUnary classifierReal
    budgetReg budgetConsumerRoute budgetConsumerPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierReal
  have budgetRegSeqUnary : UnaryHistory budgetRegSeq :=
    unary_cont_closed budgetWindowUnary budgetDyadicUnary budgetReg
  have budgetConsumerUnary : UnaryHistory budgetConsumer :=
    unary_cont_closed budgetRegSeqUnary budgetSealUnary budgetConsumerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row classifier ∨ hsame row budgetRegSeq ∨ hsame row budgetConsumer ∨
            hsame row realSeal)
        (fun row : BHist =>
          hsame row classifier ∨ hsame row budgetRegSeq ∨ hsame row budgetConsumer ∨
            Cont classifier routes realSeal)
        (fun row : BHist =>
          PkgSig bundle budgetConsumer pkg ∧
            (hsame row classifier ∨ hsame row budgetRegSeq ∨ hsame row budgetConsumer ∨
              hsame row realSeal))
        hsame := {
    core := {
      carrier_inhabited :=
        ⟨classifier, Or.inl (hsame_refl classifier)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' left right
        exact hsame_trans left right
      carrier_respects_equiv := by
        intro row other same source
        cases source with
        | inl h =>
            exact Or.inl (hsame_trans (hsame_symm same) h)
        | inr rest =>
            cases rest with
            | inl h =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) h))
            | inr rest' =>
                cases rest' with
                | inl h =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm same) h)))
                | inr h =>
                    exact Or.inr (Or.inr (Or.inr (hsame_trans (hsame_symm same) h)))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl h =>
          exact Or.inl h
      | inr rest =>
          cases rest with
          | inl h =>
              exact Or.inr (Or.inl h)
          | inr rest' =>
              cases rest' with
              | inl h =>
                  exact Or.inr (Or.inr (Or.inl h))
              | inr _h =>
                  exact Or.inr (Or.inr (Or.inr classifierReal))
    ledger_sound := by
      intro _row source
      exact ⟨budgetConsumerPkg, source⟩
  }
  exact
    ⟨cert, productUnary, classifierUnary, realSealUnary, budgetRegSeqUnary,
      budgetConsumerUnary, classifierRoute, classifierReal, budgetReg, budgetConsumerRoute,
      namePkg, budgetConsumerPkg⟩

end BEDC.Derived.CauchyProductUp
