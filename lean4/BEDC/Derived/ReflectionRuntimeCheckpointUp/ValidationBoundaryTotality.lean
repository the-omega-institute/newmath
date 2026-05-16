import BEDC.Derived.ReflectionRuntimeCheckpointUp.Certificate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectionRuntimeCheckpointCarrier_validation_boundary_totality [AskSetup]
    [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead
      validationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName ->
      hsame checkpointRead localName ->
        PkgSig bundle checkpointRead pkg ->
          Cont checkpointRead validation validationRead ->
            UnaryHistory validationRead ∧ UnaryHistory input ∧ UnaryHistory state ∧
              UnaryHistory trace ∧ UnaryHistory validation ∧ Cont input state trace ∧
                Cont trace validation route ∧ hsame checkpointRead (append provenance validation) ∧
                  hsame validationRead (append checkpointRead validation) ∧
                    PkgSig bundle checkpointRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier checkpointSame checkpointPkg validationRoute
  have obligations :=
    ReflectionRuntimeCheckpointCarrier_namecert_obligations
      (input := input) (state := state) (trace := trace) (validation := validation)
      (transport := transport) (route := route) (provenance := provenance)
      (localName := localName) (checkpointRead := checkpointRead) (bundle := bundle)
      (pkg := pkg) carrier checkpointSame checkpointPkg
  obtain ⟨inputUnary, stateUnary, traceUnary, validationUnary, checkpointUnary,
    inputStateTrace, traceValidationRoute, _provenanceValidationLocalName,
    checkpointMatchesValidation, checkpointPkg'⟩ := obligations
  have validationReadUnary : UnaryHistory validationRead :=
    unary_cont_closed checkpointUnary validationUnary validationRoute
  have validationReadMatches : hsame validationRead (append checkpointRead validation) :=
    validationRoute
  exact
    ⟨validationReadUnary, inputUnary, stateUnary, traceUnary, validationUnary, inputStateTrace,
      traceValidationRoute, checkpointMatchesValidation, validationReadMatches, checkpointPkg'⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
