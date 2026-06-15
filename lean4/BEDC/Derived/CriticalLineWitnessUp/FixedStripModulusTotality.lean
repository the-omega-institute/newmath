import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_modulus_totality
    {Z S M R Q H C P N stripRead modulusRead fixedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont modulusRead N fixedRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory N ∧ UnaryHistory stripRead ∧
                UnaryHistory modulusRead ∧ UnaryHistory fixedRead ∧ hsame H (append Z S) ∧
                  Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
                    Cont modulusRead N fixedRead ∧ Cont M R Q ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute modulusRoute fixedRoute
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
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed stripUnary unaryQ modulusRoute
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed modulusUnary unaryN fixedRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryN, stripUnary, modulusUnary,
      fixedUnary, sameH, stripRoute, modulusRoute, fixedRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
