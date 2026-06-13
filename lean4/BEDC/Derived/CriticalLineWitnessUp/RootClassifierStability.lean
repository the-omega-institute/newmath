import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_classifier_stability
    {Z S M R Q H C P N classifierRead replayRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont H C classifierRead ->
        Cont classifierRead P replayRead ->
          UnaryHistory classifierRead ∧ UnaryHistory replayRead ∧ hsame H (append Z S) ∧
            Cont H C classifierRead ∧ Cont classifierRead P replayRead ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame UnaryHistory
  intro packet classifierRoute replayRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryH unaryC classifierRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed classifierUnary unaryP replayRoute
  exact
    ⟨classifierUnary, replayUnary, sameH, classifierRoute, replayRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
