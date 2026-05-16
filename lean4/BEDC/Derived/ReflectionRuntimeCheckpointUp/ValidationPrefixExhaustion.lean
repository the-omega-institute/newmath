import BEDC.Derived.ReflectionRuntimeCheckpointUp.ValidationBoundaryTotality

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_validation_prefix_exhaustion [AskSetup]
    [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead
      validationRead routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName ->
      hsame checkpointRead localName ->
        PkgSig bundle checkpointRead pkg ->
          Cont checkpointRead validation validationRead ->
            Cont validationRead transport routed ->
              UnaryHistory input ∧ UnaryHistory state ∧ UnaryHistory trace ∧
                UnaryHistory validation ∧ UnaryHistory validationRead ∧
                  UnaryHistory routed ∧ Cont input state trace ∧
                    Cont trace validation route ∧ Cont checkpointRead validation validationRead ∧
                      Cont validationRead transport routed ∧
                        hsame checkpointRead (append provenance validation) ∧
                          hsame validationRead (append checkpointRead validation) ∧
                            PkgSig bundle checkpointRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier checkpointSame checkpointPkg validationRoute transportRoute
  have boundary :=
    ReflectionRuntimeCheckpointCarrier_validation_boundary_totality
      (input := input) (state := state) (trace := trace) (validation := validation)
      (transport := transport) (route := route) (provenance := provenance)
      (localName := localName) (checkpointRead := checkpointRead)
      (validationRead := validationRead) (bundle := bundle) (pkg := pkg)
      carrier checkpointSame checkpointPkg validationRoute
  obtain ⟨validationReadUnary, inputUnary, stateUnary, traceUnary, validationUnary,
    inputStateTrace, traceValidationRoute, checkpointMatchesValidation,
    validationReadMatches, checkpointPkg'⟩ := boundary
  obtain ⟨_inputUnary, _stateUnary, _traceUnary, _validationUnary, transportUnary,
    _provenanceUnary, _inputStateTrace, _traceValidationRoute,
    _provenanceValidationLocalName, _localNameMatchesValidation⟩ := carrier
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed validationReadUnary transportUnary transportRoute
  exact
    ⟨inputUnary, stateUnary, traceUnary, validationUnary, validationReadUnary, routedUnary,
      inputStateTrace, traceValidationRoute, validationRoute, transportRoute,
      checkpointMatchesValidation, validationReadMatches, checkpointPkg'⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
