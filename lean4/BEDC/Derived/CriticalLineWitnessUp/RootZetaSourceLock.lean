import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_source_lock
    {Z S M R Q H C P N zetaRead lockedRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q lockedRead ->
          Cont lockedRead N rhRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧
                UnaryHistory zetaRead ∧ UnaryHistory lockedRead ∧ UnaryHistory rhRead ∧
                  hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                    Cont zetaRead Q lockedRead ∧ Cont lockedRead N rhRead ∧
                      Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier zetaRoute lockRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS zetaRoute)
      (hsame_trans (cont_deterministic zetaRoute (cont_intro rfl)) (hsame_symm sameH))
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryZeta : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryLocked : UnaryHistory lockedRead :=
    unary_cont_closed unaryZeta unaryQ lockRoute
  have unaryRh : UnaryHistory rhRead :=
    unary_cont_closed unaryLocked unaryN rhRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryN, unaryZeta,
      unaryLocked, unaryRh, sameH, zetaRoute, lockRoute, rhRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
