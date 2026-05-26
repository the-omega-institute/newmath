import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_bisection_window_scope [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      sourceRead bracketRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont locatedInterval bisectionLedger sourceRead ->
        Cont sourceRead nestedWindow bracketRead ->
          Cont bracketRead realSeal consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory locatedInterval ∧ UnaryHistory bisectionLedger ∧
                UnaryHistory nestedWindow ∧ UnaryHistory sourceRead ∧
                  UnaryHistory bracketRead ∧ UnaryHistory consumerRead ∧
                    Cont locatedInterval bisectionLedger sourceRead ∧
                      Cont sourceRead nestedWindow bracketRead ∧
                        Cont bracketRead realSeal consumerRead ∧
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier sourceRoute bracketRoute consumerRoute consumerPkg
  obtain ⟨locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionLedgerRoute, _provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionLedgerRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed locatedUnary bisectionUnary sourceRoute
  have bracketUnary : UnaryHistory bracketRead :=
    unary_cont_closed sourceUnary nestedUnary bracketRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed bracketUnary realSealUnary consumerRoute
  exact
    ⟨locatedUnary, bisectionUnary, nestedUnary, sourceUnary, bracketUnary, consumerUnary,
      sourceRoute, bracketRoute, consumerRoute, consumerPkg⟩

end BEDC.Derived.IntermediateValueUp
