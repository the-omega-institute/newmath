import BEDC.Derived.ReflectionRuntimeCheckpointUp.ValidationBoundaryTotality

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_host_validation_nonescape [AskSetup]
    [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead
      validationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName ->
      hsame checkpointRead localName ->
        PkgSig bundle checkpointRead pkg ->
          Cont checkpointRead validation validationRead ->
            UnaryHistory input ∧ UnaryHistory state ∧ UnaryHistory trace ∧
              UnaryHistory validation ∧ UnaryHistory validationRead ∧ Cont input state trace ∧
                Cont trace validation route ∧ hsame checkpointRead (append provenance validation) ∧
                  hsame validationRead (append checkpointRead validation) ∧
                    PkgSig bundle checkpointRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier checkpointSame checkpointPkg validationRoute
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
  exact
    ⟨inputUnary, stateUnary, traceUnary, validationUnary, validationReadUnary,
      inputStateTrace, traceValidationRoute, checkpointMatchesValidation,
      validationReadMatches, checkpointPkg'⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
