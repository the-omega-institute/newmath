import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_transport_replay_namecert_route
    {Z S M R Q H C P N replayRead localRead auditRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H replayRead ->
        Cont replayRead N localRead ->
          Cont localRead P auditRead ->
            UnaryHistory replayRead ∧ UnaryHistory localRead ∧ UnaryHistory auditRead ∧
              Cont Q H replayRead ∧ Cont replayRead N localRead ∧
                Cont localRead P auditRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet replayRoute localRoute auditRoute
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
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryQ unaryH replayRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed replayUnary unaryN localRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed localUnary unaryP auditRoute
  exact
    ⟨replayUnary, localUnary, auditUnary, replayRoute, localRoute, auditRoute, sameH,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
