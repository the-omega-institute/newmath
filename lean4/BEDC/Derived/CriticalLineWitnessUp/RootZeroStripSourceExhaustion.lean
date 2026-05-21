import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_readback_row
    {Z S M R Q H C P N modulusRead replayRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead H replayRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory modulusRead ∧ UnaryHistory replayRead ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont M R modulusRead ∧
                Cont modulusRead H replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet modulusRoute replayRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed modulusUnary unaryH replayRoute
  exact
    ⟨unaryM, unaryR, unaryQ, unaryH, modulusUnary, replayUnary, sameH, routeQ, routeC,
      routeN, modulusRoute, replayRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
