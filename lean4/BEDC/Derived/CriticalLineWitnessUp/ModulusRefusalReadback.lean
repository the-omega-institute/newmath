import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_refusal_readback
    {Z S M R Q H C P N modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead N refusalRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory modulusRead ∧
            UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont M R modulusRead ∧ Cont modulusRead N refusalRead ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet modulusRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryModulusRead routeClosure.right.right.left refusalRoute
  exact
    ⟨unaryM, unaryR, routeClosure.left, unaryModulusRead, unaryRefusalRead, sameH,
      routeQ, modulusRoute, refusalRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
