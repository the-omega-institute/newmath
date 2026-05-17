import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_diagonal_pullback_functoriality
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal diagonalTail terminalSection : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal H diagonalTail ->
          Cont terminal E terminalSection ->
            PkgSig bundle terminalSection pkg ->
              PkgSig bundle diagonalTail pkg ->
                UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
                  UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory terminal ∧
                    UnaryHistory diagonalTail ∧ UnaryHistory terminalSection ∧ Cont B S W ∧
                      Cont W D R ∧ Cont R E terminal ∧ Cont terminal H diagonalTail ∧
                        Cont terminal E terminalSection ∧ hsame N E ∧
                          PkgSig bundle terminalSection pkg ∧
                            PkgSig bundle diagonalTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier terminalRoute diagonalRoute sectionRoute sectionPkg diagonalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, routeW, routeR, _routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryDiagonalTail : UnaryHistory diagonalTail :=
    unary_cont_closed unaryTerminal unaryH diagonalRoute
  have unaryTerminalSection : UnaryHistory terminalSection :=
    unary_cont_closed unaryTerminal unaryE sectionRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryTerminal,
      unaryDiagonalTail, unaryTerminalSection, routeW, routeR, terminalRoute,
      diagonalRoute, sectionRoute, sameName, sectionPkg, diagonalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
