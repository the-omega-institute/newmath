import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_window_nonescape
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal status : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal H status ->
          PkgSig bundle terminal pkg ->
            PkgSig bundle status pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row status ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row status ∧ Cont B S W ∧ Cont W D R ∧
                    Cont R E terminal ∧ Cont terminal H status)
                (fun row : BHist =>
                  hsame row status ∧ PkgSig bundle terminal pkg ∧
                    PkgSig bundle status pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier terminalRoute statusRoute terminalPkg statusPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, budgetRoute, windowRoute,
    _sealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryStatus : UnaryHistory status :=
    unary_cont_closed unaryTerminal unaryH statusRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro status ⟨hsame_refl status, unaryStatus⟩
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
      exact ⟨source.left, budgetRoute, windowRoute, terminalRoute, statusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg, statusPkg⟩
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp
