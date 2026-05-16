import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_budget_approximation_pullback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N R0 WA DA EA SA pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E SA ->
        Cont WA DA EA ->
          Cont SA H pullbackRead ->
            hsame W WA ->
              hsame D DA ->
                hsame R R0 ->
                  hsame E SA ->
                    PkgSig bundle SA pkg ->
                      PkgSig bundle pullbackRead pkg ->
                        UnaryHistory W /\ UnaryHistory D /\ UnaryHistory R /\
                          UnaryHistory E /\ UnaryHistory SA /\
                            UnaryHistory pullbackRead /\ Cont R E SA /\
                              Cont WA DA EA /\ Cont SA H pullbackRead /\
                                hsame W WA /\ hsame D DA /\ hsame R R0 /\
                                  hsame E SA /\ PkgSig bundle SA pkg /\
                                    PkgSig bundle pullbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute approximationRoute pullbackRoute sameW sameD sameR sameE saPkg
    pullbackPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, budgetRoute, regularRoute,
    _sealCarrier, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have unarySA : UnaryHistory SA :=
    unary_cont_closed unaryR unaryE sealRoute
  have unaryPullbackRead : UnaryHistory pullbackRead :=
    unary_cont_closed unarySA unaryH pullbackRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unarySA, unaryPullbackRead, sealRoute,
      approximationRoute, pullbackRoute, sameW, sameD, sameR, sameE, saPkg, pullbackPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
