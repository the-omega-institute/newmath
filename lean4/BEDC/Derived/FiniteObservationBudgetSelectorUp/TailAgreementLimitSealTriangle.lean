import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_tail_agreement_limit_seal_triangle
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N RQ SQ WQ DQ AQ X SL DL G EL terminal triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E terminal →
        Cont terminal AQ triangleRead →
          hsame W WQ →
            hsame D DQ →
              hsame R RQ →
                hsame E AQ →
                  hsame X R →
                    hsame SL W →
                      hsame DL D →
                        hsame EL E →
                          PkgSig bundle terminal pkg →
                            PkgSig bundle triangleRead pkg →
                              UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
                                UnaryHistory E ∧ UnaryHistory terminal ∧
                                  UnaryHistory triangleRead ∧ Cont B S W ∧
                                    Cont W D R ∧ Cont R E terminal ∧
                                      Cont terminal AQ triangleRead ∧ hsame W WQ ∧
                                        hsame D DQ ∧ hsame R RQ ∧ hsame E AQ ∧
                                          hsame X R ∧ hsame SL W ∧ hsame DL D ∧
                                            hsame EL E ∧ PkgSig bundle terminal pkg ∧
                                              PkgSig bundle triangleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRoute triangleRoute sameWindow sameDyadic sameRegular sameAgreement
    sameRoot sameLimitSource sameLimitDyadic sameLimitEndpoint terminalPkg trianglePkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, dyadicRoute,
    _selectorSealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD dyadicRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryAgreement : UnaryHistory AQ :=
    unary_transport unaryE sameAgreement
  have unaryTriangle : UnaryHistory triangleRead :=
    unary_cont_closed unaryTerminal unaryAgreement triangleRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryTerminal, unaryTriangle, budgetRoute,
      dyadicRoute, terminalRoute, triangleRoute, sameWindow, sameDyadic, sameRegular,
      sameAgreement, sameRoot, sameLimitSource, sameLimitDyadic, sameLimitEndpoint,
      terminalPkg, trianglePkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
