import BEDC.Derived.BaireCategoryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategory_finite_meet_density_handoff [AskSetup] [PackageSetup]
    {B M D O R T H C P N meetRead denseRead threadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead →
      Cont R T threadRead →
        Cont denseRead R meetRead →
          PkgSig bundle P pkg →
            PkgSig bundle meetRead pkg →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory R →
                    UnaryHistory T →
                      UnaryHistory denseRead ∧ UnaryHistory threadRead ∧
                        UnaryHistory meetRead ∧ Cont D O denseRead ∧
                          Cont R T threadRead ∧ Cont denseRead R meetRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle meetRead pkg ∧
                              baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                                [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro denseRoute threadRoute meetRoute packageP meetPkg denseUnary openUnary refinementUnary
    threadUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed denseReadUnary refinementUnary meetRoute
  exact
    ⟨denseReadUnary, threadReadUnary, meetReadUnary, denseRoute, threadRoute, meetRoute,
      packageP, meetPkg, rfl⟩

end BEDC.Derived.BaireCategoryUp
