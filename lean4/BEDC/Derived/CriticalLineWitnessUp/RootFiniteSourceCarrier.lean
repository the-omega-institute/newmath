import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootFiniteSourceCarrier {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
          hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, unaryH, routeClosure.right.left,
      routeClosure.right.right.left, routeClosure.right.right.right, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
