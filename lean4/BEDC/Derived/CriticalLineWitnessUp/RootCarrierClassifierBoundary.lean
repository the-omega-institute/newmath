import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_carrier_classifier_boundary
    {Z S M R Q H C P N rootRead classifierRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S rootRead ->
        Cont rootRead Q classifierRead ->
          Cont classifierRead N boundaryRead ->
            UnaryHistory rootRead ∧ UnaryHistory classifierRead ∧
              UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧ Cont Z S rootRead ∧
                Cont rootRead Q classifierRead ∧ Cont classifierRead N boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet rootRoute classifierRoute boundaryRoute
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
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryZ unaryS rootRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed rootUnary unaryQ classifierRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed classifierUnary unaryN boundaryRoute
  exact
    ⟨rootUnary, classifierUnary, boundaryUnary, sameH, rootRoute, classifierRoute,
      boundaryRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
