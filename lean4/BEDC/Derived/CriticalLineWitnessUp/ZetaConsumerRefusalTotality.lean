import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_consumer_refusal_totality
    {Z S M R Q H C P N stripRead modulusRead zetaRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M R modulusRead ->
          Cont stripRead modulusRead zetaRead ->
            Cont N Q refusalRead ->
              UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧ UnaryHistory zetaRead ∧
                UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont Z S stripRead ∧
                  Cont M R Q ∧ Cont M R modulusRead ∧
                    Cont stripRead modulusRead zetaRead ∧ Cont N Q refusalRead ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute modulusRoute zetaRoute refusalRoute
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
    unary_cont_closed unaryM unaryR modulusRoute
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed stripUnary modulusUnary zetaRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  exact
    ⟨stripUnary, modulusUnary, zetaUnary, refusalUnary, sameH, stripRoute, routeQ,
      modulusRoute, zetaRoute, refusalRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
