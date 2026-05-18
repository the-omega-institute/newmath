import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_tail_meet_synchronization
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N tailMeet cofinal terminalSync : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E tailMeet ->
        Cont R E cofinal ->
          Cont tailMeet cofinal terminalSync ->
            PkgSig bundle tailMeet pkg ->
              PkgSig bundle cofinal pkg ->
                PkgSig bundle terminalSync pkg ->
                  UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
                    UnaryHistory tailMeet ∧ UnaryHistory cofinal ∧
                      UnaryHistory terminalSync ∧ hsame tailMeet cofinal ∧
                        Cont B S W ∧ Cont W D R ∧ Cont R E tailMeet ∧
                          Cont R E cofinal ∧ Cont tailMeet cofinal terminalSync ∧
                            hsame N E ∧ PkgSig bundle terminalSync pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier tailMeetRoute cofinalRoute terminalRoute _tailMeetPkg _cofinalPkg terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeW, routeR, _routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTailMeet : UnaryHistory tailMeet :=
    unary_cont_closed unaryR unaryE tailMeetRoute
  have unaryCofinal : UnaryHistory cofinal :=
    unary_cont_closed unaryR unaryE cofinalRoute
  have unaryTerminal : UnaryHistory terminalSync :=
    unary_cont_closed unaryTailMeet unaryCofinal terminalRoute
  have sameTailCofinal : hsame tailMeet cofinal :=
    cont_deterministic tailMeetRoute cofinalRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryTailMeet, unaryCofinal, unaryTerminal,
      sameTailCofinal, routeW, routeR, tailMeetRoute, cofinalRoute, terminalRoute,
      sameName, terminalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
