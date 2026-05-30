import BEDC.Derived.BaireCategoryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_cauchy_thread_limit_handoff [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead threadRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead ->
      Cont R T threadRead ->
        Cont threadRead M limitRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle limitRead pkg ->
              UnaryHistory D ->
                UnaryHistory O ->
                  UnaryHistory R ->
                    UnaryHistory T ->
                      UnaryHistory M ->
                        UnaryHistory denseRead ∧ UnaryHistory threadRead ∧
                          UnaryHistory limitRead ∧ Cont D O denseRead ∧
                            Cont R T threadRead ∧ Cont threadRead M limitRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle limitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro denseRoute threadRoute limitRoute packageP limitPkg denseUnary openUnary
    refinementUnary threadUnary metricUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed threadReadUnary metricUnary limitRoute
  exact
    ⟨denseReadUnary, threadReadUnary, limitReadUnary, denseRoute, threadRoute, limitRoute,
      packageP, limitPkg⟩

end BEDC.Derived.BaireCategoryUp
