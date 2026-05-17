import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_selector_synchronization
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N selectorSeal uniformSeal terminalSync : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E selectorSeal ->
        Cont R E uniformSeal ->
          Cont selectorSeal uniformSeal terminalSync ->
            PkgSig bundle selectorSeal pkg ->
              PkgSig bundle uniformSeal pkg ->
                PkgSig bundle terminalSync pkg ->
                  UnaryHistory W /\ UnaryHistory D /\ UnaryHistory R /\
                    UnaryHistory E /\ UnaryHistory selectorSeal /\
                      UnaryHistory uniformSeal /\ UnaryHistory terminalSync /\
                        Cont B S W /\ Cont W D R /\ Cont R E selectorSeal /\
                          Cont R E uniformSeal /\
                            Cont selectorSeal uniformSeal terminalSync /\ hsame N E /\
                              PkgSig bundle terminalSync pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier selectorRoute uniformRoute syncRoute _selectorPkg _uniformPkg terminalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, windowRoute,
    _regularRoute, sameEndpoint⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowRoute
  have unarySelectorSeal : UnaryHistory selectorSeal :=
    unary_cont_closed unaryR unaryE selectorRoute
  have unaryUniformSeal : UnaryHistory uniformSeal :=
    unary_cont_closed unaryR unaryE uniformRoute
  have unaryTerminalSync : UnaryHistory terminalSync :=
    unary_cont_closed unarySelectorSeal unaryUniformSeal syncRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unarySelectorSeal, unaryUniformSeal,
      unaryTerminalSync, budgetRoute, windowRoute, selectorRoute, uniformRoute, syncRoute,
      sameEndpoint, terminalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
