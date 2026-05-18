import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_window_seal_inversion
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N seal0 seal1 routeJoin : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E seal0 ->
        Cont R E seal1 ->
          Cont seal0 seal1 routeJoin ->
            PkgSig bundle seal0 pkg ->
              PkgSig bundle seal1 pkg ->
                PkgSig bundle routeJoin pkg ->
                  hsame seal0 seal1 ∧ UnaryHistory W ∧ UnaryHistory D ∧
                    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory seal0 ∧
                      UnaryHistory seal1 ∧ UnaryHistory routeJoin ∧ Cont B S W ∧
                        Cont W D R ∧ Cont R E seal0 ∧ Cont R E seal1 ∧
                          Cont seal0 seal1 routeJoin ∧ hsame N E ∧
                            PkgSig bundle routeJoin pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute0 sealRoute1 joinRoute _sealPkg0 _sealPkg1 joinPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeW, routeR, _routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unarySeal0 : UnaryHistory seal0 :=
    unary_cont_closed unaryR unaryE sealRoute0
  have unarySeal1 : UnaryHistory seal1 :=
    unary_cont_closed unaryR unaryE sealRoute1
  have unaryJoin : UnaryHistory routeJoin :=
    unary_cont_closed unarySeal0 unarySeal1 joinRoute
  have sameSeals : hsame seal0 seal1 :=
    cont_deterministic sealRoute0 sealRoute1
  exact
    ⟨sameSeals, unaryW, unaryD, unaryR, unaryE, unarySeal0, unarySeal1, unaryJoin,
      routeW, routeR, sealRoute0, sealRoute1, joinRoute, sameName, joinPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
