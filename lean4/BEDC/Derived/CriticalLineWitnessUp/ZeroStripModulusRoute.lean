import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_modulus_route
    {Z S M R Q H C P N zetaRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory zetaRead ∧
              UnaryHistory modulusRead ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                Cont zetaRead Q modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zetaRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZetaRead unaryQ modulusRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryZetaRead, unaryModulusRead,
      sameH, zetaRoute, modulusRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_zero_strip_route_factorization
    {Z S M R Q H C P N zeroStripRead preModulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont zeroStripRead H preModulusRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
            UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory zeroStripRead ∧
              UnaryHistory preModulusRead ∧ hsame H (append Z S) ∧
                Cont Z S zeroStripRead ∧ Cont zeroStripRead H preModulusRead ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroStripRoute preModulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceBaseUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceBaseUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have preModulusUnary : UnaryHistory preModulusRead :=
    unary_cont_closed zeroStripUnary unaryH preModulusRoute
  exact
    ⟨unaryZ, unaryS, unaryH, unaryC, unaryP, unaryN, zeroStripUnary,
      preModulusUnary, sameH, zeroStripRoute, preModulusRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
