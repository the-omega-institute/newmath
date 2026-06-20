import BEDC.Derived.RegulatedIntegralUp.TasteGate

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegulatedIntegralKernelSourceScope
    {I G A S D R E H C P N stepRead compatibilityRead realRead scopeRead : BHist} :
    RegulatedIntegralCarrier I G A S D R E H C P N →
      Cont A S stepRead →
        Cont stepRead D compatibilityRead →
          Cont compatibilityRead R realRead →
            Cont realRead H scopeRead →
              UnaryHistory compatibilityRead ∧ UnaryHistory realRead ∧
                UnaryHistory scopeRead ∧ Cont A S stepRead ∧
                  Cont stepRead D compatibilityRead ∧ Cont compatibilityRead R realRead ∧
                    Cont realRead H scopeRead := by
  -- BEDC touchpoint anchor: RegulatedIntegralCarrier BHist Cont UnaryHistory
  intro carrier stepRoute compatibilityRoute realRoute scopeRoute
  obtain ⟨_intervalUnary, _integrandUnary, approximationUnary, stepPrimitiveUnary,
    darbouxsUnary, realUnary, _errorUnary, handoffUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _intervalApproximationRoute, _stepCompatibilityRoute,
    _realHandoffRoute⟩ := carrier
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed approximationUnary stepPrimitiveUnary stepRoute
  have compatibilityUnary : UnaryHistory compatibilityRead :=
    unary_cont_closed stepReadUnary darbouxsUnary compatibilityRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed compatibilityUnary realUnary realRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed realReadUnary handoffUnary scopeRoute
  exact
    ⟨compatibilityUnary, realReadUnary, scopeUnary, stepRoute, compatibilityRoute,
      realRoute, scopeRoute⟩

end BEDC.Derived.RegulatedIntegralUp
