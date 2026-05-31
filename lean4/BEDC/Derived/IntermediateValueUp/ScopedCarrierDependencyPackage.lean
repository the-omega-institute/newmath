import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueScopedCarrierDependencyPackage [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      signWindow signReplay retainedRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont locatedInterval continuousMap signWindow ->
        Cont signWindow modulusBudget signReplay ->
          Cont bisectionLedger nestedWindow retainedRead ->
            Cont retainedRead realSeal consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory locatedInterval ∧ UnaryHistory continuousMap ∧
                  UnaryHistory modulusBudget ∧ UnaryHistory bisectionLedger ∧
                    UnaryHistory nestedWindow ∧ UnaryHistory realSeal ∧
                      UnaryHistory signWindow ∧ UnaryHistory signReplay ∧
                        UnaryHistory retainedRead ∧ UnaryHistory consumerRead ∧
                          Cont locatedInterval continuousMap signWindow ∧
                            Cont signWindow modulusBudget signReplay ∧
                              Cont bisectionLedger nestedWindow retainedRead ∧
                                Cont retainedRead realSeal consumerRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localNameCert pkg ∧
                                      PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier locatedContinuousSign signModulusReplay bisectionNestedRetained
    retainedRealConsumer consumerPkg
  obtain ⟨locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedReal, provenancePkg,
    localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedReal
  have signWindowUnary : UnaryHistory signWindow :=
    unary_cont_closed locatedUnary continuousUnary locatedContinuousSign
  have signReplayUnary : UnaryHistory signReplay :=
    unary_cont_closed signWindowUnary modulusUnary signModulusReplay
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedRetained
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed retainedUnary realSealUnary retainedRealConsumer
  exact
    ⟨locatedUnary, continuousUnary, modulusUnary, bisectionUnary, nestedUnary, realSealUnary,
      signWindowUnary, signReplayUnary, retainedUnary, consumerUnary, locatedContinuousSign,
      signModulusReplay, bisectionNestedRetained, retainedRealConsumer, provenancePkg,
      localNameCertPkg, consumerPkg⟩

end BEDC.Derived.IntermediateValueUp
