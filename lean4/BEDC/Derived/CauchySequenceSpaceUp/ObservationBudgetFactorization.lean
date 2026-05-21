import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_public_observation_budget_factorization [AskSetup]
    [PackageSetup]
    {family schedule window tolerance completion transport route name observation
      budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont schedule window observation ->
        Cont observation tolerance budgetRead ->
          PkgSig bundle budgetRead pkg ->
            UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
              UnaryHistory tolerance ∧ UnaryHistory observation ∧ UnaryHistory budgetRead ∧
                Cont schedule window observation ∧ Cont observation tolerance budgetRead ∧
                  PkgSig bundle route pkg ∧ PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier observationRoute budgetRoute budgetPkg
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, _completionUnary,
    _transportUnary, _routeUnary, _nameUnary, _familyScheduleWindow,
    _windowToleranceCompletion, _completionTransportRoute, routePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed scheduleUnary windowUnary observationRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed observationUnary toleranceUnary budgetRoute
  exact
    ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, observationUnary, budgetUnary,
      observationRoute, budgetRoute, routePkg, budgetPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
