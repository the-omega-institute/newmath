import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessFiniteSourceLatticeBoundary
    {Z S M R Q H C P N zetaRead modulusRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          Cont (append Z S) Q rootRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory zetaRead ∧ UnaryHistory modulusRead ∧ UnaryHistory rootRead ∧
                  hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                    Cont zetaRead Q modulusRead ∧ Cont (append Z S) Q rootRead ∧
                      Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zetaRoute modulusRoute rootRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zetaUnary routeClosure.left modulusRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary routeClosure.left rootRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, unaryH, routeClosure.right.left,
      routeClosure.right.right.left, zetaUnary, modulusUnary, rootUnary,
      routeClosure.right.right.right, zetaRoute, modulusRoute, rootRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
