import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_real_window_nonescape
    {Z S M R Q H C P N stripRead refusalRead realWindow l10Read : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont N Q refusalRead ->
          Cont M R realWindow ->
            Cont realWindow C l10Read ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory stripRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory realWindow ∧ UnaryHistory l10Read ∧ hsame H (append Z S) ∧
                    Cont Z S stripRead ∧ Cont N Q refusalRead ∧ Cont M R realWindow ∧
                      Cont realWindow C l10Read ∧ Cont M R Q ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute refusalRoute realRoute l10Route
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
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have realUnary : UnaryHistory realWindow :=
    unary_cont_closed unaryM unaryR realRoute
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed realUnary unaryC l10Route
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, stripUnary, refusalUnary, realUnary,
      l10Unary, sameH, stripRoute, refusalRoute, realRoute, l10Route, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
