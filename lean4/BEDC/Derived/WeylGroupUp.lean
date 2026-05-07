import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp

theorem WeylGroupSimpleReflectionWord_closure
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {alpha beta reflected word action : BHist}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        GroupSingletonCarrier word ->
          Cont alpha beta reflected ->
            Cont reflected word action -> UnaryHistory reflected ∧ UnaryHistory action := by
  intro alphaCarrier betaCarrier wordCarrier reflectionRow actionRow
  have reflectedUnary : UnaryHistory reflected :=
    RootSystemReflectionClosure_result_unary vector_unary alphaCarrier betaCarrier reflectionRow
  have wordUnary : UnaryHistory word :=
    unary_transport unary_empty (hsame_symm wordCarrier)
  have actionUnary : UnaryHistory action :=
    unary_cont_closed reflectedUnary wordUnary actionRow
  exact And.intro reflectedUnary actionUnary

end BEDC.Derived.WeylGroupUp
