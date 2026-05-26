import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_sign_change_ledger [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      signWindow signReplay branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont locatedInterval continuousMap signWindow ->
        Cont signWindow modulusBudget signReplay ->
          Cont signReplay bisectionLedger branchRead ->
            PkgSig bundle branchRead pkg ->
              UnaryHistory endpointNegative ∧ UnaryHistory endpointPositive ∧
                UnaryHistory signWindow ∧ UnaryHistory signReplay ∧
                  UnaryHistory branchRead ∧ Cont locatedInterval continuousMap signWindow ∧
                    Cont signWindow modulusBudget signReplay ∧
                      Cont signReplay bisectionLedger branchRead ∧
                        Cont modulusBudget bisectionLedger nestedWindow ∧
                          Cont bisectionLedger nestedWindow realSeal ∧
                            PkgSig bundle branchRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier locatedContinuousSign signModulusReplay signBisectionBranch branchPkg
  obtain ⟨locatedUnary, endpointNegativeUnary, endpointPositiveUnary, continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedSeal, _provenancePkg,
    _localNameCertPkg⟩ := carrier
  have signWindowUnary : UnaryHistory signWindow :=
    unary_cont_closed locatedUnary continuousUnary locatedContinuousSign
  have signReplayUnary : UnaryHistory signReplay :=
    unary_cont_closed signWindowUnary modulusUnary signModulusReplay
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signReplayUnary bisectionUnary signBisectionBranch
  exact
    ⟨endpointNegativeUnary, endpointPositiveUnary, signWindowUnary, signReplayUnary,
      branchReadUnary, locatedContinuousSign, signModulusReplay, signBisectionBranch,
      modulusBisectionNested, bisectionNestedSeal, branchPkg⟩

end BEDC.Derived.IntermediateValueUp
