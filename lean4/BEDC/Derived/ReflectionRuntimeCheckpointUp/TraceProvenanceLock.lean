import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_trace_provenance_lock [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead
      traceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName ->
      hsame checkpointRead localName ->
        PkgSig bundle checkpointRead pkg ->
          Cont trace provenance traceRead ->
            UnaryHistory trace ∧ UnaryHistory provenance ∧ UnaryHistory traceRead ∧
              Cont input state trace ∧ Cont trace provenance traceRead ∧
                hsame checkpointRead (append provenance validation) ∧
                  PkgSig bundle checkpointRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier checkpointSame checkpointPkg traceProvenanceRoute
  have obligations :=
    ReflectionRuntimeCheckpointCarrier_namecert_obligations
      (input := input) (state := state) (trace := trace) (validation := validation)
      (transport := transport) (route := route) (provenance := provenance)
      (localName := localName) (checkpointRead := checkpointRead) (bundle := bundle)
      (pkg := pkg) carrier checkpointSame checkpointPkg
  obtain ⟨_inputUnary, _stateUnary, traceUnary, _validationUnary, _checkpointUnary,
    inputStateTrace, _traceValidationRoute, _provenanceValidationLocalName,
    checkpointMatchesValidation, checkpointPkg'⟩ := obligations
  obtain ⟨_carrierInputUnary, _carrierStateUnary, _carrierTraceUnary, _carrierValidationUnary,
    _transportUnary, provenanceUnary, _carrierInputStateTrace, _carrierTraceValidationRoute,
    _carrierProvenanceValidationLocalName, _carrierLocalNameMatchesValidation⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary provenanceUnary traceProvenanceRoute
  exact
    ⟨traceUnary, provenanceUnary, traceReadUnary, inputStateTrace, traceProvenanceRoute,
      checkpointMatchesValidation, checkpointPkg'⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
