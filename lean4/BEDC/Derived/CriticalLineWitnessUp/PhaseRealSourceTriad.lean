import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPhaseRealSourceTriad
    {Z S M R Q H C P N fixedStrip phaseReal regSeq streamName : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S fixedStrip ->
        Cont fixedStrip M phaseReal ->
          Cont phaseReal R regSeq ->
            Cont regSeq Q streamName ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory fixedStrip ∧ UnaryHistory phaseReal ∧
                  UnaryHistory regSeq ∧ UnaryHistory streamName ∧ hsame H (append Z S) ∧
                    Cont Z S fixedStrip ∧ Cont fixedStrip M phaseReal ∧
                      Cont phaseReal R regSeq ∧ Cont regSeq Q streamName := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet fixedStripRoute phaseRealRoute regSeqRoute streamNameRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have fixedStripUnary : UnaryHistory fixedStrip :=
    unary_cont_closed unaryZ unaryS fixedStripRoute
  have phaseRealUnary : UnaryHistory phaseReal :=
    unary_cont_closed fixedStripUnary unaryM phaseRealRoute
  have regSeqUnary : UnaryHistory regSeq :=
    unary_cont_closed phaseRealUnary unaryR regSeqRoute
  have streamNameUnary : UnaryHistory streamName :=
    unary_cont_closed regSeqUnary routeClosure.left streamNameRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, fixedStripUnary,
      phaseRealUnary, regSeqUnary, streamNameUnary, routeClosure.right.right.right,
      fixedStripRoute, phaseRealRoute, regSeqRoute, streamNameRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
