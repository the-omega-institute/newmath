import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_nonescape
    {Z S M R Q H C P N stripRead modulusRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont modulusRead N boundaryRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧
              UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧
                  Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
                    Cont modulusRead N boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute modulusRoute boundaryRoute
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
  have unaryStrip : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryModulus : UnaryHistory modulusRead :=
    unary_cont_closed unaryStrip unaryQ modulusRoute
  have unaryBoundary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryModulus unaryN boundaryRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryStrip, unaryModulus, unaryBoundary, sameH, stripRoute,
      modulusRoute, boundaryRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
