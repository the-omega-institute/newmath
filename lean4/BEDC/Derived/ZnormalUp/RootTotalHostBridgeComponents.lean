import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_total_host_bridge_components [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name bridgeRead
      hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed normal bridgeRead ->
        Cont bridgeRead continuation hostRead ->
          PkgSig bundle bridgeRead pkg ->
            PkgSig bundle hostRead pkg ->
              UnaryHistory typed ∧ UnaryHistory normal ∧ UnaryHistory continuation ∧
                UnaryHistory bridgeRead ∧ UnaryHistory hostRead ∧
                  Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
                    Cont typed normal bridgeRead ∧
                      Cont bridgeRead continuation hostRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle bridgeRead pkg ∧ PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet typedNormalBridge bridgeContinuationHost bridgePkg hostPkg
  obtain ⟨typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, _provenancePkg⟩ :=
    packet
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed typedUnary normalUnary typedNormalBridge
  have hostUnary : UnaryHistory hostRead :=
    unary_cont_closed bridgeUnary continuationUnary bridgeContinuationHost
  exact
    ⟨typedUnary, normalUnary, continuationUnary, bridgeUnary, hostUnary,
      typedFuelTerminal, terminalNormalContinuation, typedNormalBridge,
      bridgeContinuationHost, namePkg, bridgePkg, hostPkg⟩

end BEDC.Derived.ZnormalUp
