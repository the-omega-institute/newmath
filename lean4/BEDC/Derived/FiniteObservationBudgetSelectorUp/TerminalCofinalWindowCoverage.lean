import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_cofinal_window_coverage
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
                FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
                  hsame row cofinal)
              (fun _row : BHist =>
                Cont B S W ∧ Cont W D R ∧ Cont R E terminal ∧
                  Cont terminal H cofinal ∧ PkgSig bundle cofinal pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier terminalRoute cofinalRoute cofinalPkg
  have carrierPacket := carrier
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, routeW, routeR, _routeC,
    _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryCofinal : UnaryHistory cofinal :=
    unary_cont_closed unaryTerminal unaryH cofinalRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro cofinal ⟨hsame_refl cofinal, unaryCofinal⟩
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
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨carrierPacket, source.left⟩
    ledger_sound := by
      intro _row _source
      exact ⟨routeW, routeR, terminalRoute, cofinalRoute, cofinalPkg⟩
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp
