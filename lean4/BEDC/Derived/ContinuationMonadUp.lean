import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ContinuationMonadCarrier (A B C f g u _H K L N : BHist) : Prop :=
  UnaryHistory A ∧ UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory u ∧
    Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧ hsame N L

theorem ContinuationMonadCarrier_route_closure {A B C f g u H K L N : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧ hsame N L := by
  intro packet
  have unaryA : UnaryHistory A :=
    packet.left
  have unaryF : UnaryHistory f :=
    packet.right.left
  have unaryG : UnaryHistory g :=
    packet.right.right.left
  have unaryU : UnaryHistory u :=
    packet.right.right.right.left
  have routeB : Cont A f B :=
    packet.right.right.right.right.left
  have routeC : Cont B g C :=
    packet.right.right.right.right.right.left
  have routeK : Cont f g K :=
    packet.right.right.right.right.right.right.left
  have routeL : Cont K u L :=
    packet.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame N L :=
    packet.right.right.right.right.right.right.right.right
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  exact ⟨unaryB, unaryC, unaryK, unaryL, sameEndpoint⟩

theorem ContinuationMonadCarrier_kleisli_associativity_surface
    {A B C f g u H K L N read : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N read ->
        UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧
          UnaryHistory read ∧ hsame N L ∧ Cont L N read := by
  intro carrier routeRead
  have closure :
      UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧ hsame N L :=
    ContinuationMonadCarrier_route_closure carrier
  have unaryL : UnaryHistory L :=
    closure.right.right.right.left
  have sameEndpoint : hsame N L :=
    closure.right.right.right.right
  have unaryN : UnaryHistory N := by
    cases sameEndpoint
    exact unaryL
  have unaryRead : UnaryHistory read :=
    unary_cont_closed unaryL unaryN routeRead
  exact
    ⟨closure.left, closure.right.left, closure.right.right.left, unaryL, unaryRead,
      sameEndpoint, routeRead⟩

end BEDC.Derived.ContinuationMonadUp
