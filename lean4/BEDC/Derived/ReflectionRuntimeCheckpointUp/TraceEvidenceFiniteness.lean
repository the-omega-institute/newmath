import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_trace_evidence_finiteness [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName traceRead support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName →
      Cont trace route traceRead →
        Cont traceRead localName support →
          PkgSig bundle support pkg →
            UnaryHistory trace ∧ UnaryHistory traceRead ∧ UnaryHistory support ∧
              Cont trace route traceRead ∧ Cont traceRead localName support ∧
                PkgSig bundle support pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier traceRoute traceReadLocalName supportPkg
  obtain ⟨_inputUnary, _stateUnary, traceUnary, validationUnary, _transportUnary,
    _provenanceUnary, _inputStateTrace, _traceValidationTransport, _traceValidationRoute,
    _transportRouteProvenance, provenanceValidationLocalName,
    _localNameMatchesValidation⟩ := carrier
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed _provenanceUnary validationUnary provenanceValidationLocalName
  have routeUnary : UnaryHistory route :=
    unary_cont_closed traceUnary validationUnary _traceValidationRoute
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRoute
  have supportUnary : UnaryHistory support :=
    unary_cont_closed traceReadUnary localNameUnary traceReadLocalName
  exact
    ⟨traceUnary, traceReadUnary, supportUnary, traceRoute, traceReadLocalName,
      supportPkg⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
