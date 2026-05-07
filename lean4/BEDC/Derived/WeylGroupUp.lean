import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp

theorem WeylGroupSimpleReflectionWord_closure_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {alpha beta reflected word product : BHist}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        Cont alpha beta reflected -> GroupSingletonCarrier word ->
          Cont reflected word product ->
            UnaryHistory reflected ∧ UnaryHistory product ∧
              RootSystemFiniteSupportCarrier support Vector Nonzero alpha ∧
                GroupSingletonCarrier word ∧ Cont reflected word product := by
  intro alphaCarrier betaCarrier reflectionRoute wordCarrier productRoute
  have reflectedUnary : UnaryHistory reflected :=
    RootSystemReflectionClosure_result_unary vector_unary alphaCarrier betaCarrier reflectionRoute
  have wordUnary : UnaryHistory word :=
    unary_transport unary_empty (hsame_symm wordCarrier)
  have productUnary : UnaryHistory product :=
    unary_cont_closed reflectedUnary wordUnary productRoute
  exact And.intro reflectedUnary
    (And.intro productUnary
      (And.intro alphaCarrier (And.intro wordCarrier productRoute)))

def WeylGroupRootSystemGroupCarrier
    (support : ProbeBundle BHist)
    (Vector Nonzero : BHist -> Prop)
    (root word endpoint : BHist) : Prop :=
  RootSystemFiniteSupportCarrier support Vector Nonzero root ∧ GroupSingletonCarrier word ∧
    Cont root word endpoint

theorem WeylGroupRootSystemGroupCarrier_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root word endpoint : BHist} :
    WeylGroupRootSystemGroupCarrier support Vector Nonzero root word endpoint ->
      RootSystemFiniteSupportCarrier support Vector Nonzero root ∧ GroupSingletonCarrier word ∧
        Cont root word endpoint ∧ hsame endpoint root := by
  intro carrier
  have sameEndpointRoot : hsame endpoint root := by
    cases carrier.right.left
    exact cont_right_unit_result carrier.right.right
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right sameEndpointRoot))

end BEDC.Derived.WeylGroupUp
