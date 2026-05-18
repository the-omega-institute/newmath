import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ReflectionRuntimeCheckpointCarrier_validation_nonescape_route
    {I S T V H C P N validation : BHist} :
    ReflectionRuntimeCheckpointCarrier I S T V H C P N ->
      Cont V H validation ->
        hsame P N ->
          Cont I S T ∧ Cont T V H ∧ Cont V H validation ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier validationRoute sameProvenanceName
  obtain ⟨_inputUnary, _stateUnary, _traceUnary, _validationUnary, _transportUnary,
    _provenanceUnary, inputStateTrace, traceValidationTransport, _traceValidationRoute,
    _transportRouteProvenance, _provenanceValidationLocalName,
    _localNameMatchesValidation⟩ := carrier
  exact ⟨inputStateTrace, traceValidationTransport, validationRoute, sameProvenanceName⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
