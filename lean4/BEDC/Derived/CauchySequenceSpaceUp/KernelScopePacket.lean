import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_kernel_scope_packet [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route _provenance localName kernelRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
        localName bundle pkg ->
      Cont family schedule kernelRead ->
        Cont kernelRead completion completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
              UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory kernelRead ∧
                UnaryHistory completionRead ∧ Cont family schedule kernelRead ∧
                  Cont kernelRead completion completionRead ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier kernelCont completionCont completionPkg
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary,
    _transportUnary, _routeUnary, _nameUnary, _storedWindow, _storedCompletion, _storedRoute,
    _routePkg, namePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed familyUnary scheduleUnary kernelCont
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed kernelUnary completionUnary completionCont
  exact
    ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary, kernelUnary,
      completionReadUnary, kernelCont, completionCont, namePkg, completionPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
