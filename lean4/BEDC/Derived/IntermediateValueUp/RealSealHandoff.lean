import BEDC.Derived.IntermediateValueUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont nestedWindow realSeal consumerRead ->
        PkgSig bundle consumerRead pkg ->
          UnaryHistory locatedInterval ∧ UnaryHistory bisectionLedger ∧
            UnaryHistory nestedWindow ∧ UnaryHistory realSeal ∧ UnaryHistory consumerRead ∧
              Cont modulusBudget bisectionLedger nestedWindow ∧
                Cont bisectionLedger nestedWindow realSeal ∧
                  Cont nestedWindow realSeal consumerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier nestedSealConsumer consumerPkg
  obtain ⟨locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedSeal, provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedSeal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed nestedUnary realSealUnary nestedSealConsumer
  exact
    ⟨locatedUnary, bisectionUnary, nestedUnary, realSealUnary, consumerUnary,
      modulusBisectionNested, bisectionNestedSeal, nestedSealConsumer, provenancePkg,
      consumerPkg⟩

end BEDC.Derived.IntermediateValueUp
