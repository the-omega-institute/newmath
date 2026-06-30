import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_rh_refusal
    {Z S M R Q H C P N windowRead modulusRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S windowRead ->
        Cont windowRead Q modulusRead ->
          Cont modulusRead N rhRead ->
            UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧ UnaryHistory rhRead ∧
              hsame H (append Z S) ∧ Cont Z S windowRead ∧
                Cont windowRead Q modulusRead ∧ Cont modulusRead N rhRead ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet windowRoute modulusRoute rhRoute
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
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryZ unaryS windowRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary unaryQ modulusRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed modulusUnary unaryN rhRoute
  exact
    ⟨windowUnary, modulusUnary, rhUnary, sameH, windowRoute, modulusRoute, rhRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
