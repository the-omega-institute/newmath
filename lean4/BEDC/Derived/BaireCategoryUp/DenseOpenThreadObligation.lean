import BEDC.Derived.BaireCategoryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_dense_open_thread_obligation [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead refinementRead threadRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead ->
      Cont denseRead R refinementRead ->
        Cont refinementRead T threadRead ->
          Cont threadRead M limitRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle limitRead pkg ->
                UnaryHistory B ->
                  UnaryHistory M ->
                    UnaryHistory D ->
                      UnaryHistory O ->
                        UnaryHistory R ->
                          UnaryHistory T ->
                            UnaryHistory denseRead ∧ UnaryHistory refinementRead ∧
                              UnaryHistory threadRead ∧ UnaryHistory limitRead ∧
                                Cont D O denseRead ∧ Cont denseRead R refinementRead ∧
                                  Cont refinementRead T threadRead ∧
                                    Cont threadRead M limitRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle limitRead pkg ∧
                                        baireCategoryFields
                                            (BaireCategoryUp.mk B M D O R T H C P N) =
                                          [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro denseRoute refinementRoute threadRoute limitRoute packageP limitPkg _baseUnary
    metricUnary denseUnary openUnary refinementUnary threadUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed denseReadUnary refinementUnary refinementRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementReadUnary threadUnary threadRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed threadReadUnary metricUnary limitRoute
  exact
    ⟨denseReadUnary, refinementReadUnary, threadReadUnary, limitReadUnary, denseRoute,
      refinementRoute, threadRoute, limitRoute, packageP, limitPkg, rfl⟩

end BEDC.Derived.BaireCategoryUp
