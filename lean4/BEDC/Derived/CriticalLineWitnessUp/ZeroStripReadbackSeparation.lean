import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_readback_separation
    {Z S M R Q H C P N zeroStripRead fixedStripRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont (append Z S) M fixedStripRead ->
          Cont N Q refusalRead ->
            UnaryHistory zeroStripRead ∧ UnaryHistory fixedStripRead ∧
              UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                Cont Z S zeroStripRead ∧ Cont (append Z S) M fixedStripRead ∧
                  Cont N Q refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroStripRoute fixedStripRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have fixedStripUnary : UnaryHistory fixedStripRead :=
    unary_cont_closed unaryAppend unaryM fixedStripRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  exact
    ⟨zeroStripUnary, fixedStripUnary, refusalUnary, sameH, zeroStripRoute,
      fixedStripRoute, refusalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
