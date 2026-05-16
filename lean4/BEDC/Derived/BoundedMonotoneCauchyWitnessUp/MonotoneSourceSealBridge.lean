import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_monotone_source_seal_bridge [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      monotoneRead bridgeRead sealBridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source regular monotoneRead ->
        Cont monotoneRead sealRow bridgeRead ->
          Cont bridgeRead provenance sealBridgeRead ->
            PkgSig bundle sealBridgeRead pkg ->
              UnaryHistory monotoneRead ∧ UnaryHistory bridgeRead ∧
                UnaryHistory sealBridgeRead ∧ Cont source regular monotoneRead ∧
                  Cont monotoneRead sealRow bridgeRead ∧
                    Cont bridgeRead provenance sealBridgeRead ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle sealBridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularMonotone monotoneSealBridge bridgeProvenanceSeal sealBridgePkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularMonotone
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed monotoneUnary sealUnary monotoneSealBridge
  have sealBridgeUnary : UnaryHistory sealBridgeRead :=
    unary_cont_closed bridgeUnary provenanceUnary bridgeProvenanceSeal
  exact
    ⟨monotoneUnary, bridgeUnary, sealBridgeUnary, sourceRegularMonotone,
      monotoneSealBridge, bridgeProvenanceSeal, provenancePkg, sealBridgePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
