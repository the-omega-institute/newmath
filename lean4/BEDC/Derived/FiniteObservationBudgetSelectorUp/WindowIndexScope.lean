import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp.WindowIndexScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_window_index_scope
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N windowIndex : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont W D windowIndex ->
        PkgSig bundle windowIndex pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row windowIndex ∧ UnaryHistory row)
            (fun row : BHist => hsame row windowIndex ∧ Cont B S W ∧ Cont W D windowIndex)
            (fun row : BHist => PkgSig bundle windowIndex pkg ∧ hsame row windowIndex ∧
              hsame N E)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier windowRoute pkgSig
  obtain ⟨unaryB, unaryS, unaryD, _unaryE, _unaryH, budgetRoute, _dyadicRoute,
    _sealRoute, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryWindowIndex : UnaryHistory windowIndex :=
    unary_cont_closed unaryW unaryD windowRoute
  have sourceWindowIndex :
      (fun row : BHist => hsame row windowIndex ∧ UnaryHistory row) windowIndex := by
    exact And.intro (hsame_refl windowIndex) unaryWindowIndex
  exact {
    core := {
      carrier_inhabited := Exists.intro windowIndex sourceWindowIndex
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
        intro row other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left)
          (unary_transport source.right same)
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, budgetRoute, windowRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨pkgSig, source.left, sameName⟩
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp.WindowIndexScope
