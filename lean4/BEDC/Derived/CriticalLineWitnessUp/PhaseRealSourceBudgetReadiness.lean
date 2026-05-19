import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_source_budget_readiness
    {Z S M R Q H C P N stripRead phaseReal regSeq budgetRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead M phaseReal ->
          Cont phaseReal C regSeq ->
            Cont regSeq N budgetRead ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory stripRead ∧
                  UnaryHistory phaseReal ∧ UnaryHistory regSeq ∧ UnaryHistory budgetRead ∧
                    hsame H (append Z S) ∧ Cont Z S stripRead ∧
                      Cont stripRead M phaseReal ∧ Cont phaseReal C regSeq ∧
                        Cont regSeq N budgetRead ∧ Cont M R Q ∧ Cont Q H C ∧
                          Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute phaseRoute regSeqRoute budgetRoute
  have carrierPacket := packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrierPacket
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have phaseUnary : UnaryHistory phaseReal :=
    unary_cont_closed stripUnary unaryM phaseRoute
  have regSeqUnary : UnaryHistory regSeq :=
    unary_cont_closed phaseUnary routeClosure.right.left regSeqRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed regSeqUnary routeClosure.right.right.left budgetRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, stripUnary, phaseUnary, regSeqUnary, budgetUnary, sameH,
      stripRoute, phaseRoute, regSeqRoute, budgetRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
