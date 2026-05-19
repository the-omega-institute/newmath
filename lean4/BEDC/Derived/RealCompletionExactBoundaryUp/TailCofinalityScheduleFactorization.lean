import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryTailCofinalityScheduleFactorization [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N boundaryRead scheduleRead combinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory K ->
        UnaryHistory J ->
          UnaryHistory S ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    Cont W R boundaryRead ->
                      Cont D E scheduleRead ->
                        Cont boundaryRead scheduleRead combinedRead ->
                          PkgSig bundle combinedRead pkg ->
                            realCompletionExactBoundaryFields
                                (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                              [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                              UnaryHistory boundaryRead ∧ UnaryHistory scheduleRead ∧
                                UnaryHistory combinedRead ∧ Cont W R boundaryRead ∧
                                  Cont D E scheduleRead ∧
                                    Cont boundaryRead scheduleRead combinedRead ∧
                                      PkgSig bundle combinedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro _unaryL _unaryK _unaryJ _unaryS unaryW unaryR unaryD unaryE boundaryCont
    scheduleCont combinedCont combinedPkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryW unaryR boundaryCont
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryD unaryE scheduleCont
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed boundaryUnary scheduleUnary combinedCont
  exact
    ⟨rfl, boundaryUnary, scheduleUnary, combinedUnary, boundaryCont, scheduleCont,
      combinedCont, combinedPkg⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
