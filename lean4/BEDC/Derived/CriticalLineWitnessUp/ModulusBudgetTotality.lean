import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_budget_totality
    {Z S M R Q H C P N fixedStrip phaseReal regSeq streamName sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S fixedStrip ->
        Cont fixedStrip M phaseReal ->
          Cont phaseReal R regSeq ->
            Cont regSeq Q streamName ->
              Cont streamName C sourceRead ->
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory fixedStrip ∧ UnaryHistory phaseReal ∧
                    UnaryHistory regSeq ∧ UnaryHistory streamName ∧
                      UnaryHistory sourceRead ∧ hsame H (append Z S) ∧
                        Cont Z S fixedStrip ∧ Cont fixedStrip M phaseReal ∧
                          Cont phaseReal R regSeq ∧ Cont regSeq Q streamName ∧
                            Cont streamName C sourceRead ∧ Cont M R Q ∧ Cont Q H C ∧
                              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet fixedStripRoute phaseRealRoute regSeqRoute streamNameRoute sourceReadRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have fixedStripUnary : UnaryHistory fixedStrip :=
    unary_cont_closed unaryZ unaryS fixedStripRoute
  have phaseRealUnary : UnaryHistory phaseReal :=
    unary_cont_closed fixedStripUnary unaryM phaseRealRoute
  have regSeqUnary : UnaryHistory regSeq :=
    unary_cont_closed phaseRealUnary unaryR regSeqRoute
  have streamNameUnary : UnaryHistory streamName :=
    unary_cont_closed regSeqUnary routeClosure.left streamNameRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed streamNameUnary routeClosure.right.left sourceReadRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, fixedStripUnary, phaseRealUnary,
      regSeqUnary, streamNameUnary, sourceReadUnary, sameH, fixedStripRoute, phaseRealRoute,
      regSeqRoute, streamNameRoute, sourceReadRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
