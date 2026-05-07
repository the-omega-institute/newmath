import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp

theorem WeylGroupSimpleReflection_word_closure_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {alpha beta reflected word product : BHist}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        Cont alpha beta reflected -> GroupSingletonCarrier word ->
          Cont word BHist.Empty product ->
            UnaryHistory reflected ∧ GroupSingletonCarrier product ∧ hsame product word ∧
              Cont alpha beta reflected := by
  intro alphaCarrier betaCarrier reflectionRoute wordCarrier wordProduct
  have reflectedUnary : UnaryHistory reflected :=
    RootSystemReflectionClosure_result_unary vector_unary alphaCarrier betaCarrier reflectionRoute
  have productWord : hsame product word :=
    cont_right_unit_result wordProduct
  have productCarrier : GroupSingletonCarrier product :=
    hsame_trans productWord wordCarrier
  exact And.intro reflectedUnary
    (And.intro productCarrier (And.intro productWord reflectionRoute))

end BEDC.Derived.WeylGroupUp
