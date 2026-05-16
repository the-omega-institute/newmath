import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_public_export [AskSetup] [PackageSetup]
    {B S W D R E H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
            UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory publicRead ∧ Cont B S W ∧
              Cont W D R ∧ Cont R E publicRead ∧ hsame N E ∧
                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg hsame
  intro carrier publicRoute publicPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, windowRoute,
    _sealRoute, sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryR unaryE publicRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryPublicRead, budgetRoute,
      windowRoute, publicRoute, sameName, publicPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
