import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_regseqrat_route_readiness
    {Z S M R Q H C P N regseqRead realRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q R regseqRead ->
        Cont regseqRead M realRead ->
          UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory regseqRead ∧
            UnaryHistory realRead ∧ hsame H (append Z S) ∧ Cont Q R regseqRead ∧
              Cont regseqRead M realRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet regseqRoute realRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed routeClosure.left unaryR regseqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary unaryM realRoute
  exact
    ⟨routeClosure.left, unaryR, unaryM, regseqUnary, realUnary,
      routeClosure.right.right.right, regseqRoute, realRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
