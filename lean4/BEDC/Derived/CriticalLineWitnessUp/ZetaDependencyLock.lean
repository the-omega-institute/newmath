import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_dependency_lock
    {Z S M R Q H C P N zetaSource zeroRead rationalRead realRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaSource ->
        Cont zetaSource Q zeroRead ->
          Cont M R rationalRead ->
            Cont rationalRead H realRead ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory zetaSource ∧ UnaryHistory zeroRead ∧
                  UnaryHistory rationalRead ∧ UnaryHistory realRead ∧
                    hsame H (append Z S) ∧ Cont Z S zetaSource ∧
                      Cont zetaSource Q zeroRead ∧ Cont M R rationalRead ∧
                        Cont rationalRead H realRead ∧ Cont M R Q ∧ Cont Q H C ∧
                          Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zetaRoute zeroRoute rationalRoute realRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have zetaUnary : UnaryHistory zetaSource :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed zetaUnary unaryQ zeroRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed unaryM unaryR rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary unaryH realRoute
  exact
    ⟨unaryZ,
      unaryS,
      unaryM,
      unaryR,
      unaryQ,
      zetaUnary,
      zeroUnary,
      rationalUnary,
      realUnary,
      sameH,
      zetaRoute,
      zeroRoute,
      rationalRoute,
      realRoute,
      routeQ,
      routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
