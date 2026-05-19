import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_source_triad
    {Z S M R Q H C P N stripRead phaseReal regSeq streamName sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q phaseReal ->
          Cont phaseReal H regSeq ->
            Cont regSeq Q streamName ->
              Cont streamName C sourceRead ->
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                  UnaryHistory C ∧ UnaryHistory stripRead ∧ UnaryHistory phaseReal ∧
                    UnaryHistory regSeq ∧ UnaryHistory streamName ∧ UnaryHistory sourceRead ∧
                      hsame H (append Z S) ∧ Cont Z S stripRead ∧
                        Cont stripRead Q phaseReal ∧ Cont phaseReal H regSeq ∧
                          Cont regSeq Q streamName ∧ Cont streamName C sourceRead ∧
                            Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier stripRoute phaseRealRoute regSeqRoute streamNameRoute sourceRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrier
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have stripReadUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have phaseRealUnary : UnaryHistory phaseReal :=
    unary_cont_closed stripReadUnary routeClosure.left phaseRealRoute
  have regSeqUnary : UnaryHistory regSeq :=
    unary_cont_closed phaseRealUnary unaryH regSeqRoute
  have streamNameUnary : UnaryHistory streamName :=
    unary_cont_closed regSeqUnary routeClosure.left streamNameRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed streamNameUnary routeClosure.right.left sourceRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, unaryH, routeClosure.right.left,
      stripReadUnary, phaseRealUnary, regSeqUnary, streamNameUnary, sourceReadUnary,
      routeClosure.right.right.right, stripRoute, phaseRealRoute, regSeqRoute,
      streamNameRoute, sourceRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
