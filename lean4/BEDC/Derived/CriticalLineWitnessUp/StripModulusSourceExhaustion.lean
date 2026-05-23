import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_strip_modulus_source_exhaustion
    {Z S M R Q H C P N zetaRead modulusRead refusalRead terminal : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont refusalRead C terminal ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory zetaRead ∧
                  UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory terminal ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                      Cont zetaRead Q modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧
                        Cont C P N ∧ Cont N Q refusalRead ∧
                          Cont refusalRead C terminal := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zetaRoute modulusRoute refusalRoute terminalRoute
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
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zetaUnary unaryQ modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed refusalUnary unaryC terminalRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, zetaUnary, modulusUnary,
      refusalUnary, terminalUnary, sameH, zetaRoute, modulusRoute, routeQ, routeC, routeN,
      refusalRoute, terminalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
