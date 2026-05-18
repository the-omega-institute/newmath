import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterTerminalLeanTargetSurface
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N windowRead regularRead tailRead sealRead terminal : BHist} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D windowRead ->
        Cont windowRead R regularRead ->
          Cont regularRead B tailRead ->
            Cont tailRead E sealRead ->
              Cont sealRead N terminal ->
                UnaryHistory windowRead /\ UnaryHistory regularRead /\
                  UnaryHistory tailRead /\ UnaryHistory sealRead /\
                    UnaryHistory terminal /\ Cont S D windowRead /\
                      Cont windowRead R regularRead /\ Cont regularRead B tailRead /\
                        Cont tailRead E sealRead /\ Cont sealRead N terminal := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier windowRoute regularRoute tailRoute sealRoute terminalRoute
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryH, _unaryC, routeR, _routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryS unaryD windowRoute
  have unaryRegular : UnaryHistory regularRead :=
    unary_cont_closed unaryWindow unaryR regularRoute
  have unaryTail : UnaryHistory tailRead :=
    unary_cont_closed unaryRegular unaryB tailRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryTail unaryE sealRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unarySeal unaryN terminalRoute
  exact
    ⟨unaryWindow, unaryRegular, unaryTail, unarySeal, unaryTerminal, windowRoute,
      regularRoute, tailRoute, sealRoute, terminalRoute⟩

end BEDC.Derived.FiniteTailFilterUp
