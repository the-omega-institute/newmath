import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_strip_classifier_obligation
    {Z S M R Q H C P N stripRead classifierRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q classifierRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory stripRead ∧
            UnaryHistory classifierRead ∧ hsame H (append Z S) ∧ Cont Z S stripRead ∧
              Cont stripRead Q classifierRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute classifierRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed stripUnary routeClosure.left classifierRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, stripUnary, classifierUnary,
      routeClosure.right.right.right, stripRoute, classifierRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
