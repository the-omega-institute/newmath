import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp.CauchyLimitSealPullback

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_cauchy_limit_seal_pullback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N SL DL G EL selectorSeal sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E selectorSeal →
        Cont G EL sealRead →
          hsame W SL →
            hsame D DL →
              hsame R G →
                hsame E EL →
                  PkgSig bundle selectorSeal pkg →
                    PkgSig bundle sealRead pkg →
                      UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
                        UnaryHistory E ∧ UnaryHistory G ∧ UnaryHistory EL ∧
                          UnaryHistory selectorSeal ∧ UnaryHistory sealRead ∧
                            Cont B S W ∧ Cont W D R ∧ Cont R E selectorSeal ∧
                              Cont G EL sealRead ∧ hsame W SL ∧ hsame D DL ∧
                                hsame R G ∧ hsame E EL ∧ hsame selectorSeal sealRead ∧
                                  PkgSig bundle selectorSeal pkg ∧
                                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier selectorRoute sealRoute sameWindow sameDyadic sameRegular sameSeal
    selectorPkg sealPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, dyadicRoute,
    _carrierSealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD dyadicRoute
  have unaryG : UnaryHistory G :=
    unary_transport unaryR sameRegular
  have unaryEL : UnaryHistory EL :=
    unary_transport unaryE sameSeal
  have selectorUnary : UnaryHistory selectorSeal :=
    unary_cont_closed unaryR unaryE selectorRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryG unaryEL sealRoute
  have sameSelectorSeal : hsame selectorSeal sealRead :=
    cont_respects_hsame sameRegular sameSeal selectorRoute sealRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryG, unaryEL, selectorUnary, sealUnary,
      budgetRoute, dyadicRoute, selectorRoute, sealRoute, sameWindow, sameDyadic,
      sameRegular, sameSeal, sameSelectorSeal, selectorPkg, sealPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp.CauchyLimitSealPullback
