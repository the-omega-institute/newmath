import BEDC.Derived.RegularCauchyFilterUp

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFilterCarrier_tail_stability [AskSetup] [PackageSetup]
    (B R T D M E H C P N windowA windowB commonTail : BHist) :
    regularCauchyFilterFromEventFlow
          (regularCauchyFilterToEventFlow (RegularCauchyFilterUp.mk B R T D M E H C P N)) =
        some (RegularCauchyFilterUp.mk B R T D M E H C P N) ->
      UnaryHistory T ->
        UnaryHistory D ->
          Cont T D windowA ->
            Cont T D windowB ->
              Cont windowA windowB commonTail ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory commonTail ∧
                  Cont T D windowA ∧ Cont T D windowB ∧ Cont windowA windowB commonTail ∧
                    hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  intro _decoded tUnary dUnary windowARoute windowBRoute commonTailRoute
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed tUnary dUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed tUnary dUnary windowBRoute
  have commonTailUnary : UnaryHistory commonTail :=
    unary_cont_closed windowAUnary windowBUnary commonTailRoute
  exact
    ⟨windowAUnary, windowBUnary, commonTailUnary, windowARoute, windowBRoute,
      commonTailRoute, hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩

end BEDC.Derived.RegularCauchyFilterUp
