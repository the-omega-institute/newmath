import BEDC.Derived.RegulatedIntegralUp.TasteGate

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegulatedIntegralPublicInterface {I G A S D R E H C P N publicRead : BHist} :
    RegulatedIntegralCarrier I G A S D R E H C P N ->
      Cont D E publicRead ->
        hsame publicRead R ->
          UnaryHistory I ∧ UnaryHistory G ∧ UnaryHistory A ∧ UnaryHistory S ∧
            UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory publicRead ∧
              hsame publicRead R ∧ Cont I G A ∧ Cont A S D ∧
                Cont D E publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory RegulatedIntegralCarrier
  intro carrier publicRoute samePublic
  obtain ⟨intervalUnary, integrandUnary, approximationUnary, stepUnary, darbouxsUnary,
    realUnary, errorUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    intervalApproximationRoute, stepCompatibilityRoute, _realHandoffRoute⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_transport realUnary (hsame_symm samePublic)
  exact
    ⟨intervalUnary, integrandUnary, approximationUnary, stepUnary, darbouxsUnary,
      realUnary, errorUnary, publicUnary, samePublic, intervalApproximationRoute,
      stepCompatibilityRoute, publicRoute⟩

end BEDC.Derived.RegulatedIntegralUp
