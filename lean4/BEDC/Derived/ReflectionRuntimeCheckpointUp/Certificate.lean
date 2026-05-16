import BEDC.Derived.ReflectionRuntimeCheckpointUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ReflectionRuntimeCheckpointCarrier
    (input state trace validation transport route provenance localName : BHist) : Prop :=
  UnaryHistory input ∧ UnaryHistory state ∧ UnaryHistory trace ∧
    UnaryHistory validation ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont input state trace ∧ Cont trace validation route ∧
        Cont provenance validation localName ∧ hsame localName (append provenance validation)

theorem ReflectionRuntimeCheckpointCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {input state trace validation transport route provenance localName checkpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectionRuntimeCheckpointCarrier input state trace validation transport route provenance
        localName ->
      hsame checkpointRead localName ->
        PkgSig bundle checkpointRead pkg ->
          UnaryHistory input ∧ UnaryHistory state ∧ UnaryHistory trace ∧
            UnaryHistory validation ∧ UnaryHistory checkpointRead ∧
              Cont input state trace ∧ Cont trace validation route ∧
                Cont provenance validation localName ∧
                  hsame checkpointRead (append provenance validation) ∧
                    PkgSig bundle checkpointRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg
  intro carrier checkpointSame checkpointPkg
  obtain ⟨inputUnary, stateUnary, traceUnary, validationUnary, _transportUnary,
    _provenanceUnary, inputStateTrace, traceValidationRoute,
    provenanceValidationLocalName, localNameMatchesValidation⟩ := carrier
  have checkpointUnary : UnaryHistory checkpointRead :=
    unary_transport
      (unary_cont_closed _provenanceUnary validationUnary provenanceValidationLocalName)
      (hsame_symm checkpointSame)
  have checkpointMatchesValidation : hsame checkpointRead (append provenance validation) :=
    hsame_trans checkpointSame localNameMatchesValidation
  exact
    ⟨inputUnary, stateUnary, traceUnary, validationUnary, checkpointUnary, inputStateTrace,
      traceValidationRoute, provenanceValidationLocalName, checkpointMatchesValidation,
      checkpointPkg⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
