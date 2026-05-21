import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_quotient_refusal_route [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont completion name refusalRead ->
        PkgSig bundle refusalRead pkg ->
          UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
            UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory refusalRead ∧
              Cont family schedule window ∧ Cont window tolerance completion ∧
                Cont completion name refusalRead ∧ PkgSig bundle route pkg ∧
                  PkgSig bundle refusalRead pkg := by
  intro carrier completionNameRefusal refusalPkg
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary,
    _transportUnary, _routeUnary, nameUnary, familyScheduleWindow,
    windowToleranceCompletion, _completionTransportRoute, routePkg, _namePkg⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed completionUnary nameUnary completionNameRefusal
  exact
    ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary, refusalUnary,
      familyScheduleWindow, windowToleranceCompletion, completionNameRefusal, routePkg,
      refusalPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
