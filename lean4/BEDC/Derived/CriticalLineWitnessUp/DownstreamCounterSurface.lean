import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_counter_surface
    {Z S M R Q H C P N counterRead inspectionRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q counterRead ->
        Cont counterRead H inspectionRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧ UnaryHistory counterRead ∧
              UnaryHistory inspectionRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N ∧ Cont N Q counterRead ∧
                  Cont counterRead H inspectionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet counterRoute inspectionRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have counterUnary : UnaryHistory counterRead :=
    unary_cont_closed unaryN unaryQ counterRoute
  have inspectionUnary : UnaryHistory inspectionRead :=
    unary_cont_closed counterUnary unaryH inspectionRoute
  exact
    ⟨unaryZ,
      unaryS,
      unaryM,
      unaryR,
      unaryQ,
      unaryH,
      unaryN,
      counterUnary,
      inspectionUnary,
      sameH,
      routeQ,
      routeC,
      routeN,
      counterRoute,
      inspectionRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
