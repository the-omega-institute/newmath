import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp.BudgetLedgerMinimality

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_budget_ledger_minimality
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E terminal →
        PkgSig bundle terminal pkg →
          SemanticNameCert
            (fun row : BHist =>
              FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
                (hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
                  hsame row R ∨ hsame row E ∨ hsame row terminal))
            (fun row : BHist =>
              UnaryHistory row ∧ Cont B S W ∧ Cont W D R ∧ Cont R E terminal ∧
                (hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
                  hsame row R ∨ hsame row E ∨ hsame row terminal))
            (fun _row : BHist => PkgSig bundle terminal pkg ∧ hsame N E)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier terminalRoute terminalPkg
  have carrierWitness := carrier
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, windowRoute,
    _sealRoute, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have sourceB :
      (fun row : BHist =>
        FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
          (hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
            hsame row R ∨ hsame row E ∨ hsame row terminal))
        B := by
    exact And.intro carrierWitness (Or.inl (hsame_refl B))
  exact {
    core := {
      carrier_inhabited := Exists.intro B sourceB
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        refine And.intro source.left ?_
        cases source.right with
        | inl sameB =>
            exact Or.inl (hsame_trans (hsame_symm same) sameB)
        | inr rest =>
            cases rest with
            | inl sameS =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameS))
            | inr rest =>
                cases rest with
                | inl sameW =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameW)))
                | inr rest =>
                    cases rest with
                    | inl sameD =>
                        exact Or.inr
                          (Or.inr (Or.inr
                            (Or.inl (hsame_trans (hsame_symm same) sameD))))
                    | inr rest =>
                        cases rest with
                        | inl sameR =>
                            exact Or.inr
                              (Or.inr (Or.inr (Or.inr
                                (Or.inl (hsame_trans (hsame_symm same) sameR)))))
                        | inr rest =>
                            cases rest with
                            | inl sameE =>
                                exact Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inl (hsame_trans (hsame_symm same) sameE))))))
                            | inr sameTerminal =>
                                exact Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inr (hsame_trans (hsame_symm same)
                                      sameTerminal))))))
    }
    pattern_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl sameB =>
            exact unary_transport unaryB (hsame_symm sameB)
        | inr rest =>
            cases rest with
            | inl sameS =>
                exact unary_transport unaryS (hsame_symm sameS)
            | inr rest =>
                cases rest with
                | inl sameW =>
                    exact unary_transport unaryW (hsame_symm sameW)
                | inr rest =>
                    cases rest with
                    | inl sameD =>
                        exact unary_transport unaryD (hsame_symm sameD)
                    | inr rest =>
                        cases rest with
                        | inl sameR =>
                            exact unary_transport unaryR (hsame_symm sameR)
                        | inr rest =>
                            cases rest with
                            | inl sameE =>
                                exact unary_transport unaryE (hsame_symm sameE)
                            | inr sameTerminal =>
                                exact unary_transport unaryTerminal (hsame_symm sameTerminal)
      exact
        And.intro rowUnary
          (And.intro budgetRoute
            (And.intro windowRoute (And.intro terminalRoute source.right)))
    ledger_sound := by
      intro _row _source
      exact And.intro terminalPkg sameName
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp.BudgetLedgerMinimality
