import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContourIntegralOperationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ContourIntegralOperationCarrier (G F S M I H P N : BHist) : Prop :=
  UnaryHistory G ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory M ∧
    UnaryHistory P ∧ hsame H (append G F) ∧ Cont S M I ∧ Cont I P N

theorem ContourIntegralOperationCarrier_riemann_sum_route_closure {G F S M I H P N : BHist} :
    ContourIntegralOperationCarrier G F S M I H P N →
      UnaryHistory I ∧ UnaryHistory N ∧ hsame H (append G F) := by
  intro packet
  have unaryS : UnaryHistory S :=
    packet.right.right.left
  have unaryM : UnaryHistory M :=
    packet.right.right.right.left
  have unaryP : UnaryHistory P :=
    packet.right.right.right.right.left
  have sameInputFace : hsame H (append G F) :=
    packet.right.right.right.right.right.left
  have integralRoute : Cont S M I :=
    packet.right.right.right.right.right.right.left
  have exportRoute : Cont I P N :=
    packet.right.right.right.right.right.right.right
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryS unaryM integralRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryI unaryP exportRoute
  exact ⟨unaryI, unaryN, sameInputFace⟩

end BEDC.Derived.ContourIntegralOperationUp
