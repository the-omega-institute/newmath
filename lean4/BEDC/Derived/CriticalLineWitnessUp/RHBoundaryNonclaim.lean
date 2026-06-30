import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_nonclaim
    {Z S M R Q H C P N refusalRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead H rhBoundary ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory refusalRead ∧
              UnaryHistory rhBoundary ∧ hsame H (append Z S) ∧
                Cont N Q refusalRead ∧ Cont refusalRead H rhBoundary := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet refusalRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory rhBoundary :=
    unary_cont_closed refusalUnary unaryH boundaryRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, refusalUnary, boundaryUnary,
      sameH, refusalRoute, boundaryRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
