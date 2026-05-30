import BEDC.Derived.RegulatedIntegralUp.TasteGate

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegulatedIntegralRealCompletionRoute
    {I G A S D R E H C P N stepRead realRead : BHist} :
    RegulatedIntegralCarrier I G A S D R E H C P N ->
      Cont A S stepRead ->
        hsame stepRead D ->
          Cont D E realRead ->
            hsame realRead R ->
              UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory realRead ∧
                Cont A S stepRead ∧ Cont D E realRead ∧ hsame stepRead D ∧
                  hsame realRead R := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier stepRoute sameStep realRoute sameReal
  obtain ⟨_intervalUnary, _integrandUnary, _approximationUnary, _stepUnary, darbouxsUnary,
    realUnary, errorUnary, _handoffUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _intervalApproximationRoute, _stepCompatibilityRoute, _realHandoffRoute⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_transport realUnary (hsame_symm sameReal)
  exact
    ⟨darbouxsUnary, realUnary, errorUnary, realReadUnary, stepRoute, realRoute, sameStep,
      sameReal⟩

end BEDC.Derived.RegulatedIntegralUp
