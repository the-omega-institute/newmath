import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_real_seal_window_saturation
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N W' R' C' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont B S W' ->
        Cont W' D R' ->
          Cont R' E C' ->
            PkgSig bundle C' pkg ->
              UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory W' ∧
                UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory R' ∧ UnaryHistory E ∧
                  UnaryHistory C' ∧ Cont B S W' ∧ Cont W' D R' ∧ Cont R' E C' ∧
                    hsame W W' ∧ hsame R R' ∧ hsame C C' ∧ PkgSig bundle C' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier budgetRoute' regularRoute' sealRoute' sealPkg'
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    sealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryW' : UnaryHistory W' :=
    unary_cont_closed unaryB unaryS budgetRoute'
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have unaryR' : UnaryHistory R' :=
    unary_cont_closed unaryW' unaryD regularRoute'
  have unaryC' : UnaryHistory C' :=
    unary_cont_closed unaryR' unaryE sealRoute'
  have sameW : hsame W W' :=
    cont_respects_hsame (hsame_refl B) (hsame_refl S) budgetRoute budgetRoute'
  have sameR : hsame R R' :=
    cont_respects_hsame sameW (hsame_refl D) regularRoute regularRoute'
  have sameC : hsame C C' :=
    cont_respects_hsame sameR (hsame_refl E) sealRoute sealRoute'
  exact
    ⟨unaryB, unaryS, unaryW, unaryW', unaryD, unaryR, unaryR', unaryE, unaryC',
      budgetRoute', regularRoute', sealRoute', sameW, sameR, sameC, sealPkg'⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
