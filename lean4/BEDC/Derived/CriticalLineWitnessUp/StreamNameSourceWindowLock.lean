import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_streamname_source_window_lock
    {Z S M R Q H C P N sourceWindow regseqRead endpoint : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceWindow ->
        Cont sourceWindow Q regseqRead ->
          Cont regseqRead R endpoint ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory sourceWindow ∧
              UnaryHistory Q ∧ UnaryHistory regseqRead ∧ UnaryHistory endpoint ∧
                hsame H (append Z S) ∧ Cont Z S sourceWindow ∧
                  Cont sourceWindow Q regseqRead ∧ Cont regseqRead R endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceWindowRoute regseqRoute endpointRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, unaryR, _unaryP, _sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed unaryZ unaryS sourceWindowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed sourceWindowUnary routeClosure.left regseqRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed regseqUnary unaryR endpointRoute
  exact
    ⟨unaryZ, unaryS, sourceWindowUnary, routeClosure.left, regseqUnary, endpointUnary,
      routeClosure.right.right.right, sourceWindowRoute, regseqRoute, endpointRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
