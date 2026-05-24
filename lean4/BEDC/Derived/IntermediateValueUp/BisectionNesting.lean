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

theorem IntermediateValueCarrier_modulus_branch_transport [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      transportedModulus transportedBranch transportedWindow consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont modulusBudget transports transportedModulus ->
        Cont transportedModulus bisectionLedger transportedBranch ->
          Cont transportedBranch nestedWindow transportedWindow ->
            Cont transportedWindow realSeal consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory transportedModulus ∧ UnaryHistory transportedBranch ∧
                  UnaryHistory transportedWindow ∧ UnaryHistory consumerRead ∧
                    Cont transportedModulus bisectionLedger transportedBranch ∧
                      Cont transportedBranch nestedWindow transportedWindow ∧
                        Cont transportedWindow realSeal consumerRead ∧
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier modulusTransport branchTransport windowTransport consumerTransport consumerPkg
  obtain ⟨_locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionLedgerRoute, _provenancePkg,
    _localNameCertPkg⟩ := carrier
  have transportedModulusUnary : UnaryHistory transportedModulus :=
    unary_cont_closed modulusUnary transportsUnary modulusTransport
  have transportedBranchUnary : UnaryHistory transportedBranch :=
    unary_cont_closed transportedModulusUnary bisectionUnary branchTransport
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have transportedWindowUnary : UnaryHistory transportedWindow :=
    unary_cont_closed transportedBranchUnary nestedUnary windowTransport
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionLedgerRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed transportedWindowUnary realSealUnary consumerTransport
  exact
    ⟨transportedModulusUnary, transportedBranchUnary, transportedWindowUnary,
      consumerReadUnary, branchTransport, windowTransport, consumerTransport, consumerPkg⟩

end BEDC.Derived.IntermediateValueUp
