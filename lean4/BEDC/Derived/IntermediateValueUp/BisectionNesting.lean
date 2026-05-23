import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_bisection_nesting [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      retainedRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont bisectionLedger nestedWindow retainedRead ->
        Cont retainedRead routes consumerRead ->
          PkgSig bundle consumerRead pkg ->
            UnaryHistory bisectionLedger ∧ UnaryHistory nestedWindow ∧
              UnaryHistory retainedRead ∧ UnaryHistory consumerRead ∧
                Cont bisectionLedger nestedWindow realSeal ∧
                  Cont bisectionLedger nestedWindow retainedRead ∧
                    Cont retainedRead routes consumerRead ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier retainedRoute consumerRoute consumerPkg
  obtain ⟨_locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionLedgerRoute, _provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed bisectionUnary nestedUnary retainedRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed retainedUnary routesUnary consumerRoute
  exact
    ⟨bisectionUnary, nestedUnary, retainedUnary, consumerUnary, bisectionLedgerRoute,
      retainedRoute, consumerRoute, consumerPkg⟩

end BEDC.Derived.IntermediateValueUp
