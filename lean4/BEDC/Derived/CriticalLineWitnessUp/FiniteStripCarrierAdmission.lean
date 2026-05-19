import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_finite_strip_carrier_admission
    {Z S M R Q H C P N zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q zetaRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
          UnaryHistory N ∧ UnaryHistory zetaRead ∧ hsame H (append Z S) ∧
            Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q zetaRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zetaRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left zetaRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, routeClosure.right.left, routeClosure.right.right.left,
      zetaUnary, routeClosure.right.right.right, routeQ, routeC, routeN, zetaRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
