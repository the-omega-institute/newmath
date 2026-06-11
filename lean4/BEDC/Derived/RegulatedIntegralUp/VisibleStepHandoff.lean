import BEDC.Derived.RegulatedIntegralUp.TasteGate

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegulatedIntegralVisibleStepHandoff
    {I G A S D R E H C P N stepRead : BHist} :
    RegulatedIntegralCarrier I G A S D R E H C P N →
      Cont I G A →
        Cont A S stepRead →
          hsame stepRead S →
            UnaryHistory I ∧ UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory S ∧
              UnaryHistory E ∧ UnaryHistory stepRead ∧ Cont I G A ∧
                Cont A S stepRead ∧ hsame stepRead S := by
  -- BEDC touchpoint anchor: RegulatedIntegralCarrier BHist Cont hsame UnaryHistory
  intro carrier intervalIntegrand stepRoute sameStep
  obtain ⟨intervalUnary, integrandUnary, approximationUnary, stepPrimitiveUnary, _darbouxUnary,
    _realUnary, errorUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _intervalApproximationRoute, _stepCompatibilityRoute, _realHandoffRoute⟩ := carrier
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed approximationUnary stepPrimitiveUnary stepRoute
  exact
    ⟨intervalUnary, integrandUnary, approximationUnary, stepPrimitiveUnary, errorUnary,
      stepReadUnary, intervalIntegrand, stepRoute, sameStep⟩

end BEDC.Derived.RegulatedIntegralUp
