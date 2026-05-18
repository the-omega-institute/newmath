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

theorem ReflectionRuntimeCheckpointCarrier_trace_boundary_readback [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead traceRead
      boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName →
      hsame checkpointRead localName →
        PkgSig bundle checkpointRead pkg →
          Cont trace provenance traceRead →
            Cont traceRead localName boundedRead →
              PkgSig bundle boundedRead pkg →
                UnaryHistory trace ∧ UnaryHistory provenance ∧ UnaryHistory traceRead ∧
                  UnaryHistory boundedRead ∧ Cont input state trace ∧
                    Cont trace provenance traceRead ∧ Cont traceRead localName boundedRead ∧
                      hsame checkpointRead (append provenance validation) ∧
                        PkgSig bundle checkpointRead pkg ∧ PkgSig bundle boundedRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier checkpointSame checkpointPkg traceProvenanceRoute boundedRoute boundedPkg
  have locked :=
    ReflectionRuntimeCheckpointCarrier_trace_provenance_lock
      (input := input) (state := state) (trace := trace) (validation := validation)
      (transport := transport) (route := route) (provenance := provenance)
      (localName := localName) (checkpointRead := checkpointRead) (traceRead := traceRead)
      (bundle := bundle) (pkg := pkg) carrier checkpointSame checkpointPkg
      traceProvenanceRoute
  obtain ⟨traceUnary, provenanceUnary, traceReadUnary, inputStateTrace,
    traceProvenanceRoute', checkpointMatchesValidation, checkpointPkg'⟩ := locked
  have localNameUnary : UnaryHistory localName := by
    obtain ⟨_inputUnary, _stateUnary, _traceUnary, validationUnary, _transportUnary,
      _provenanceUnary, _inputStateTrace, _traceValidationRoute,
      provenanceValidationLocalName, _localNameMatchesValidation⟩ := carrier
    exact unary_cont_closed provenanceUnary validationUnary provenanceValidationLocalName
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed traceReadUnary localNameUnary boundedRoute
  exact
    ⟨traceUnary, provenanceUnary, traceReadUnary, boundedUnary, inputStateTrace,
      traceProvenanceRoute', boundedRoute, checkpointMatchesValidation, checkpointPkg',
      boundedPkg⟩

theorem ReflectionRuntimeCheckpointCarrier_state_trace_coupling [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName stateTraceRead
      validationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName ->
      Cont state trace stateTraceRead ->
        Cont stateTraceRead validation validationRead ->
          PkgSig bundle validationRead pkg ->
            UnaryHistory input ∧ UnaryHistory state ∧ UnaryHistory trace ∧
              UnaryHistory validation ∧ UnaryHistory stateTraceRead ∧
                UnaryHistory validationRead ∧ Cont input state trace ∧
                  Cont state trace stateTraceRead ∧
                    Cont stateTraceRead validation validationRead ∧
                      Cont trace validation route ∧ PkgSig bundle validationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier stateTraceRoute validationReadRoute validationReadPkg
  obtain ⟨inputUnary, stateUnary, traceUnary, validationUnary, _transportUnary,
    _provenanceUnary, inputStateTrace, traceValidationRoute,
    _provenanceValidationLocalName, _localNameMatchesValidation⟩ := carrier
  have stateTraceUnary : UnaryHistory stateTraceRead :=
    unary_cont_closed stateUnary traceUnary stateTraceRoute
  have validationReadUnary : UnaryHistory validationRead :=
    unary_cont_closed stateTraceUnary validationUnary validationReadRoute
  exact
    ⟨inputUnary, stateUnary, traceUnary, validationUnary, stateTraceUnary,
      validationReadUnary, inputStateTrace, stateTraceRoute, validationReadRoute,
      traceValidationRoute, validationReadPkg⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
