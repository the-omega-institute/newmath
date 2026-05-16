import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_shared_window_union [AskSetup] [PackageSetup]
    {B S W1 W2 D R1 R2 E H C1 C2 P N unionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W1 D R1 E H C1 P N ->
      FiniteObservationBudgetSelectorCarrier B S W2 D R2 E H C2 P N ->
        Cont W1 W2 unionRead ->
          PkgSig bundle unionRead pkg ->
            UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W1 ∧ UnaryHistory W2 ∧
              UnaryHistory unionRead ∧ UnaryHistory D ∧ UnaryHistory R1 ∧
                UnaryHistory R2 ∧ Cont B S W1 ∧ Cont B S W2 ∧
                  Cont W1 W2 unionRead ∧ hsame R1 R2 ∧ PkgSig bundle unionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro first second windowUnion unionPkg
  obtain ⟨unaryB, unaryS, unaryD, _unaryE, _unaryH, routeW1, routeR1, _routeC1,
    _sameName1⟩ := first
  obtain ⟨_unaryB2, _unaryS2, _unaryD2, _unaryE2, _unaryH2, routeW2, routeR2,
    _routeC2, _sameName2⟩ := second
  have unaryW1 : UnaryHistory W1 :=
    unary_cont_closed unaryB unaryS routeW1
  have unaryW2 : UnaryHistory W2 :=
    unary_cont_closed unaryB unaryS routeW2
  have unaryUnion : UnaryHistory unionRead :=
    unary_cont_closed unaryW1 unaryW2 windowUnion
  have unaryR1 : UnaryHistory R1 :=
    unary_cont_closed unaryW1 unaryD routeR1
  have unaryR2 : UnaryHistory R2 :=
    unary_cont_closed unaryW2 unaryD routeR2
  have sameWindow : hsame W1 W2 :=
    cont_deterministic routeW1 routeW2
  have sameRead : hsame R1 R2 :=
    cont_respects_hsame sameWindow (hsame_refl D) routeR1 routeR2
  exact
    ⟨unaryB, unaryS, unaryW1, unaryW2, unaryUnion, unaryD, unaryR1, unaryR2,
      routeW1, routeW2, windowUnion, sameRead, unionPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
