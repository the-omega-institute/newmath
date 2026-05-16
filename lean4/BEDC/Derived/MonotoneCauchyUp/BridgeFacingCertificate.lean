import BEDC.Derived.MonotoneCauchyUp
import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_bridge_facing_certificate [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      source witness trap boundedTransport boundedRoute boundedLocal monotoneRead bridgeRead
      sealBridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      BEDC.Derived.BoundedMonotoneCauchyWitnessUp.BoundedMonotoneCauchyWitnessCarrier
        source regular schedule witness ledger trap realSeal boundedTransport boundedRoute
        provenance boundedLocal bundle pkg ->
        Cont source regular monotoneRead ->
          Cont monotoneRead realSeal bridgeRead ->
            Cont bridgeRead provenance sealBridgeRead ->
              PkgSig bundle sealBridgeRead pkg ->
                UnaryHistory monotoneRead ∧ UnaryHistory bridgeRead ∧
                  UnaryHistory sealBridgeRead ∧ Cont source regular monotoneRead ∧
                    Cont monotoneRead realSeal bridgeRead ∧
                      Cont bridgeRead provenance sealBridgeRead ∧
                        Cont transportRow route provenance ∧ PkgSig bundle nameRow pkg ∧
                          PkgSig bundle sealBridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier bounded sourceRegularMonotone monotoneSealBridge bridgeProvenanceSeal
    sealPkg
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, _intervalUnary,
    _realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  obtain ⟨sourceUnary, regularUnary, _scheduleUnaryB, _witnessUnary, _ledgerUnaryB,
    _trapUnary, realSealUnary, provenanceUnary, _sourceScheduleRegular,
    _regularWitnessTrap, _trapSealRoute, _transportLocalRoute, _routeProvenanceSeal,
    _provenancePkg⟩ := bounded
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularMonotone
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed monotoneUnary realSealUnary monotoneSealBridge
  have sealBridgeUnary : UnaryHistory sealBridgeRead :=
    unary_cont_closed bridgeUnary provenanceUnary bridgeProvenanceSeal
  exact
    ⟨monotoneUnary, bridgeUnary, sealBridgeUnary, sourceRegularMonotone,
      monotoneSealBridge, bridgeProvenanceSeal, transportRouteProvenance, nameRowPkg,
      sealPkg⟩

end BEDC.Derived.MonotoneCauchyUp
