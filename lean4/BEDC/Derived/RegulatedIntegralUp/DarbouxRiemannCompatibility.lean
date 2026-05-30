import BEDC.Derived.RegulatedIntegralUp.TasteGate

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegulatedIntegralDarbouxRiemannCompatibility
    {I G A S D R E H C P N compatibilityRead : BHist} :
    RegulatedIntegralCarrier I G A S D R E H C P N →
      Cont A S compatibilityRead →
        hsame compatibilityRead D →
          UnaryHistory A ∧ UnaryHistory S ∧ UnaryHistory D ∧
            UnaryHistory compatibilityRead ∧ Cont A S D ∧
              Cont A S compatibilityRead ∧ hsame compatibilityRead D := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier compatibilityRoute sameCompatibility
  obtain ⟨_intervalUnary, _integrandUnary, approximationUnary, stepUnary, compatibilityUnary,
    _realUnary, _errorUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _intervalApproximationRoute, carrierCompatibilityRoute, _realHandoffRoute⟩ := carrier
  have compatibilityReadUnary : UnaryHistory compatibilityRead :=
    unary_transport compatibilityUnary (hsame_symm sameCompatibility)
  exact
    ⟨approximationUnary, stepUnary, compatibilityUnary, compatibilityReadUnary,
      carrierCompatibilityRoute, compatibilityRoute, sameCompatibility⟩

end BEDC.Derived.RegulatedIntegralUp
