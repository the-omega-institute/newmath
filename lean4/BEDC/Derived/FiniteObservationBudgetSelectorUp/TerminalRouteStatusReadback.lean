import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_route_status_readback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal cofinal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal H cofinal ->
          PkgSig bundle cofinal pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row cofinal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cofinal ∧ Cont B S W ∧ Cont W D R ∧
                  Cont R E terminal ∧ Cont terminal H cofinal)
              (fun row : BHist => PkgSig bundle cofinal pkg ∧ hsame row cofinal)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier terminalRoute cofinalRoute cofinalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, budgetRoute, windowRoute,
    _sealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryCofinal : UnaryHistory cofinal :=
    unary_cont_closed unaryTerminal unaryH cofinalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro cofinal ⟨hsame_refl cofinal, unaryCofinal⟩
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
      exact ⟨source.left, budgetRoute, windowRoute, terminalRoute, cofinalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨cofinalPkg, source.left⟩
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp
