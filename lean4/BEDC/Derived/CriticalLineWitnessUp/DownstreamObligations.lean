import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_source_obligation
    {Z S M R Q H C P N downstream sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q downstream ->
        Cont downstream H sourceRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
              UnaryHistory downstream ∧ UnaryHistory sourceRead ∧ hsame H (append Z S) ∧
                Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q downstream ∧
                  Cont downstream H sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet downstreamRoute sourceRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    routeClosure.left
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    routeClosure.right.left
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed unaryN unaryQ downstreamRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed downstreamUnary unaryH sourceRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, downstreamUnary,
      sourceUnary, routeClosure.right.right.right, routeQ, routeC, routeN, downstreamRoute,
      sourceRoute⟩

theorem CriticalLineWitnessCarrier_zero_strip_compatibility_obligation
    {Z S M R Q H C P N zeroStrip compatibility : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStrip ->
        Cont zeroStrip Q compatibility ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory zeroStrip ∧
            UnaryHistory compatibility ∧ hsame H (append Z S) ∧ Cont Z S zeroStrip ∧
              Cont zeroStrip Q compatibility ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroStripRoute compatibilityRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    routeClosure.left
  have zeroStripUnary : UnaryHistory zeroStrip :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have compatibilityUnary : UnaryHistory compatibility :=
    unary_cont_closed zeroStripUnary unaryQ compatibilityRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, zeroStripUnary, compatibilityUnary,
      routeClosure.right.right.right, zeroStripRoute, compatibilityRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
