import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_carrier_source_totality
    {Z S M R Q H C P N stripRead dependencyRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S stripRead →
        Cont stripRead Q dependencyRead →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory stripRead ∧
            UnaryHistory dependencyRead ∧ hsame H (append Z S) ∧ Cont Z S stripRead ∧
              Cont stripRead Q dependencyRead ∧ Cont M R Q ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier stripRoute dependencyRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrier
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have stripReadUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have dependencyReadUnary : UnaryHistory dependencyRead :=
    unary_cont_closed stripReadUnary routeClosure.left dependencyRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, stripReadUnary, dependencyReadUnary,
      routeClosure.right.right.right, stripRoute, dependencyRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
