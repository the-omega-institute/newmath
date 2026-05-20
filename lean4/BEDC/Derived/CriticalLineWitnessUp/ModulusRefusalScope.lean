import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_refusal_scope
    {Z S M R Q H C P N modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont N Q refusalRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory N ∧
            UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧
              hsame H (append Z S) ∧ Cont M R Q := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet modulusRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC,
      _routeN⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  exact
    ⟨unaryM, unaryR, routeClosure.left, routeClosure.right.right.left, modulusReadUnary,
      refusalReadUnary, sameH, routeQ⟩

end BEDC.Derived.CriticalLineWitnessUp
