import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_zeta_sibling_route
    {Z S M R Q H C P N zetaRead continuationRead zeroWitnessRead fixedStripRead
      localNameRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q continuationRead ->
          Cont continuationRead H zeroWitnessRead ->
            Cont zeroWitnessRead S fixedStripRead ->
              Cont fixedStripRead N localNameRead ->
                UnaryHistory zetaRead ∧ UnaryHistory continuationRead ∧
                  UnaryHistory zeroWitnessRead ∧ UnaryHistory fixedStripRead ∧
                    UnaryHistory localNameRead ∧ hsame H (append Z S) ∧
                      Cont Z S zetaRead ∧ Cont zetaRead Q continuationRead ∧
                        Cont continuationRead H zeroWitnessRead ∧
                          Cont zeroWitnessRead S fixedStripRead ∧
                            Cont fixedStripRead N localNameRead ∧ Cont M R Q ∧
                              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame UnaryHistory
  intro packet zetaRoute continuationRoute zeroWitnessRoute fixedStripRoute localNameRoute
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
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed zetaUnary unaryQ continuationRoute
  have zeroWitnessUnary : UnaryHistory zeroWitnessRead :=
    unary_cont_closed continuationUnary unaryH zeroWitnessRoute
  have fixedStripUnary : UnaryHistory fixedStripRead :=
    unary_cont_closed zeroWitnessUnary unaryS fixedStripRoute
  have localNameUnary : UnaryHistory localNameRead :=
    unary_cont_closed fixedStripUnary unaryN localNameRoute
  exact
    ⟨zetaUnary, continuationUnary, zeroWitnessUnary, fixedStripUnary, localNameUnary,
      sameH, zetaRoute, continuationRoute, zeroWitnessRoute, fixedStripRoute,
      localNameRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
