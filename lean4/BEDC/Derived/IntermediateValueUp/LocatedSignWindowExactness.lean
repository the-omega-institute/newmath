import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_located_sign_window_exactness [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      endpointRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont locatedInterval continuousMap endpointRead ->
        Cont endpointRead nestedWindow windowRead ->
          PkgSig bundle windowRead pkg ->
            UnaryHistory locatedInterval ∧ UnaryHistory endpointNegative ∧
              UnaryHistory endpointPositive ∧ UnaryHistory continuousMap ∧
                UnaryHistory modulusBudget ∧ UnaryHistory bisectionLedger ∧
                  UnaryHistory nestedWindow ∧ UnaryHistory endpointRead ∧
                    UnaryHistory windowRead ∧ Cont locatedInterval continuousMap endpointRead ∧
                      Cont endpointRead nestedWindow windowRead ∧
                        Cont modulusBudget bisectionLedger nestedWindow ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier endpointRoute windowRoute windowPkg
  obtain ⟨locatedUnary, endpointNegativeUnary, endpointPositiveUnary, continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, _bisectionNestedSeal, provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed locatedUnary continuousUnary endpointRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed endpointReadUnary nestedUnary windowRoute
  exact
    ⟨locatedUnary, endpointNegativeUnary, endpointPositiveUnary, continuousUnary,
      modulusUnary, bisectionUnary, nestedUnary, endpointReadUnary, windowReadUnary,
      endpointRoute, windowRoute, modulusBisectionNested, provenancePkg, windowPkg⟩

end BEDC.Derived.IntermediateValueUp
