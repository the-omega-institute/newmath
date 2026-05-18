import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ReflectionRuntimeCheckpointCarrier_audit_provenance_exhaustion
    {I S T V H C P N audit : BHist} :
    ReflectionRuntimeCheckpointCarrier I S T V H C P N ->
      Cont H C P ->
      Cont P N audit ->
          hsame P N ->
            Cont H C P ∧ Cont P N audit ∧ hsame P N ∧ hsame audit (append P N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier _routeConsumer auditRoute sameProvenanceName
  obtain ⟨_inputUnary, _stateUnary, _traceUnary, _validationUnary, _transportUnary,
    _provenanceUnary, _inputStateTrace, _traceValidationTransport, _traceValidationRoute,
    transportRouteProvenance, _provenanceValidationLocalName,
    _localNameMatchesValidation⟩ := carrier
  exact ⟨transportRouteProvenance, auditRoute, sameProvenanceName, auditRoute⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
