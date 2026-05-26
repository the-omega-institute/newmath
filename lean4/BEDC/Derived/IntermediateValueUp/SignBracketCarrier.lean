import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_sign_bracket_carrier [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert signWindow
      signReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont locatedInterval continuousMap signWindow ->
        Cont signWindow modulusBudget signReplay ->
          PkgSig bundle signReplay pkg ->
            UnaryHistory locatedInterval ∧ UnaryHistory endpointNegative ∧
              UnaryHistory endpointPositive ∧ UnaryHistory continuousMap ∧
                UnaryHistory modulusBudget ∧ UnaryHistory bisectionLedger ∧
                  UnaryHistory nestedWindow ∧ UnaryHistory signWindow ∧
                    UnaryHistory signReplay ∧ Cont locatedInterval continuousMap signWindow ∧
                      Cont signWindow modulusBudget signReplay ∧
                        Cont modulusBudget bisectionLedger nestedWindow ∧
                          Cont bisectionLedger nestedWindow realSeal ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg ∧
                              PkgSig bundle signReplay pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier locatedContinuousSign signModulusReplay signReplayPkg
  obtain ⟨locatedUnary, endpointNegativeUnary, endpointPositiveUnary, continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedSeal, provenancePkg,
    localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have signWindowUnary : UnaryHistory signWindow :=
    unary_cont_closed locatedUnary continuousUnary locatedContinuousSign
  have signReplayUnary : UnaryHistory signReplay :=
    unary_cont_closed signWindowUnary modulusUnary signModulusReplay
  exact
    ⟨locatedUnary, endpointNegativeUnary, endpointPositiveUnary, continuousUnary, modulusUnary,
      bisectionUnary, nestedUnary, signWindowUnary, signReplayUnary, locatedContinuousSign,
      signModulusReplay, modulusBisectionNested, bisectionNestedSeal, provenancePkg,
      localNameCertPkg, signReplayPkg⟩

end BEDC.Derived.IntermediateValueUp
