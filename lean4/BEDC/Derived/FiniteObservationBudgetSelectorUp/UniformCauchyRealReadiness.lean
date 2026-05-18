import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_uniform_cauchy_real_readiness
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal boundedSeal diagonalRead handoff realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal E boundedSeal ->
          Cont terminal boundedSeal diagonalRead ->
            Cont diagonalRead E handoff ->
              Cont R E realRead ->
                PkgSig bundle handoff pkg ->
                  PkgSig bundle realRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row terminal ∨ hsame row boundedSeal ∨
                            hsame row diagonalRead ∨ hsame row handoff ∨
                              hsame row realRead)
                        (fun row : BHist =>
                          PkgSig bundle handoff pkg ∧ PkgSig bundle realRead pkg ∧
                            hsame row handoff)
                        hsame ∧
                      UnaryHistory terminal ∧ UnaryHistory boundedSeal ∧
                        UnaryHistory diagonalRead ∧ UnaryHistory handoff ∧
                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readEndpoint terminalEndpoint terminalBounded diagonalEndpoint realRoute
    handoffPkg realPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    _sealRoute, _sameEndpoint⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE readEndpoint
  have boundedSealUnary : UnaryHistory boundedSeal :=
    unary_cont_closed terminalUnary unaryE terminalEndpoint
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed terminalUnary boundedSealUnary terminalBounded
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed diagonalReadUnary unaryE diagonalEndpoint
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed unaryR unaryE realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row boundedSeal ∨ hsame row diagonalRead ∨
              hsame row handoff ∨ hsame row realRead)
          (fun row : BHist =>
            PkgSig bundle handoff pkg ∧ PkgSig bundle realRead pkg ∧ hsame row handoff)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
        exact ⟨handoffPkg, realPkg, source.left⟩
    }
  exact
    ⟨cert, terminalUnary, boundedSealUnary, diagonalReadUnary, handoffUnary,
      realReadUnary⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
