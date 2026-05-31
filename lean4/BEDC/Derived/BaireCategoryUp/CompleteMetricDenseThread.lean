import BEDC.Derived.BaireCategoryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_complete_metric_dense_thread [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead threadRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead ->
      Cont R T threadRead ->
        Cont threadRead M limitRead ->
          PkgSig bundle P pkg ->
            UnaryHistory D ->
              UnaryHistory O ->
                UnaryHistory R ->
                  UnaryHistory T ->
                    UnaryHistory M ->
                      UnaryHistory denseRead ∧ UnaryHistory threadRead ∧
                        UnaryHistory limitRead ∧ Cont D O denseRead ∧
                          Cont R T threadRead ∧ Cont threadRead M limitRead ∧
                            baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                              [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro denseRoute threadRoute limitRoute _packageP denseUnary openUnary refinementUnary
    threadUnary metricUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed threadReadUnary metricUnary limitRoute
  exact
    ⟨denseReadUnary, threadReadUnary, limitReadUnary, denseRoute, threadRoute, limitRoute,
      rfl⟩

end BEDC.Derived.BaireCategoryUp
