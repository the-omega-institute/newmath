import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CriticalLineWitnessCarrier (Z S M R Q H C P N : BHist) : Prop :=
  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory P ∧
    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N

theorem CriticalLineWitnessCarrier_modulus_route_closure {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) := by
  intro packet
  have unaryZ : UnaryHistory Z :=
    packet.left
  have unaryS : UnaryHistory S :=
    packet.right.left
  have unaryM : UnaryHistory M :=
    packet.right.right.left
  have unaryR : UnaryHistory R :=
    packet.right.right.right.left
  have unaryP : UnaryHistory P :=
    packet.right.right.right.right.left
  have sameH : hsame H (append Z S) :=
    packet.right.right.right.right.right.left
  have routeQ : Cont M R Q :=
    packet.right.right.right.right.right.right.left
  have routeC : Cont Q H C :=
    packet.right.right.right.right.right.right.right.left
  have routeN : Cont C P N :=
    packet.right.right.right.right.right.right.right.right
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  exact ⟨unaryQ, unaryC, unaryN, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
