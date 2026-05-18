import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_input_state_exposure [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName stateRead
      traceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName →
      Cont input state stateRead →
        Cont stateRead trace traceRead →
          PkgSig bundle traceRead pkg →
            UnaryHistory input ∧ UnaryHistory state ∧ UnaryHistory trace ∧
              UnaryHistory stateRead ∧ UnaryHistory traceRead ∧
                Cont input state trace ∧ Cont input state stateRead ∧
                  Cont stateRead trace traceRead ∧ PkgSig bundle traceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier inputStateRead stateReadTrace traceReadPkg
  obtain ⟨inputUnary, stateUnary, traceUnary, _validationUnary, _transportUnary,
    _provenanceUnary, inputStateTrace, _traceValidationTransport, _traceValidationRoute,
    _transportRouteProvenance, _provenanceValidationLocalName,
    _localNameMatchesValidation⟩ := carrier
  have stateReadUnary : UnaryHistory stateRead :=
    unary_cont_closed inputUnary stateUnary inputStateRead
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed stateReadUnary traceUnary stateReadTrace
  exact
    ⟨inputUnary, stateUnary, traceUnary, stateReadUnary, traceReadUnary, inputStateTrace,
      inputStateRead, stateReadTrace, traceReadPkg⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
