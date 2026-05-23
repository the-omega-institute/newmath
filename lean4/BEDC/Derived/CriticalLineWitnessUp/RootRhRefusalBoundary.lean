import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_source_row
    {Z S M R Q H C P N zeroStripRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory zeroStripRead ∧
          hsame zeroStripRead H ∧ hsame H (append Z S) ∧ Cont Z S zeroStripRead ∧
            Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zeroStripRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have sameZeroStripH : hsame zeroStripRead H :=
    cont_deterministic zeroStripRoute (cont_intro sameH)
  exact
    ⟨unaryZ, unaryS, zeroStripUnary, sameZeroStripH, sameH, zeroStripRoute, routeQ,
      routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_rh_refusal_boundary
    {Z S M R Q H C P N zetaStripRead refusalRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaStripRead ->
        Cont N Q refusalRead ->
          Cont zetaStripRead refusalRead rhBoundary ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
              UnaryHistory zetaStripRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory rhBoundary ∧ hsame H (append Z S) ∧
                  Cont Z S zetaStripRead ∧ Cont N Q refusalRead ∧
                    Cont zetaStripRead refusalRead rhBoundary ∧ Cont M R Q ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaStripRoute refusalRoute boundaryRoute
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
  have zetaStripUnary : UnaryHistory zetaStripRead :=
    unary_cont_closed unaryZ unaryS zetaStripRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory rhBoundary :=
    unary_cont_closed zetaStripUnary refusalUnary boundaryRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryN, zetaStripUnary, refusalUnary, boundaryUnary,
      sameH, zetaStripRoute, refusalRoute, boundaryRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
