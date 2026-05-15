import BEDC.Derived.ApophaticNameUp.SupplyShapeNoninternalization

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_bridge_tuple_noninternalization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow supplyRead bridgeRead
      externalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg ->
      Cont request gate supplyRead ->
        PkgSig bundle supplyRead pkg ->
          Cont ledger nameRow bridgeRead ->
            PkgSig bundle bridgeRead pkg ->
              Cont bridgeRead provenance externalityRead ->
                PkgSig bundle externalityRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      ApophaticNameCarrier socket request gate ledger transport route provenance
                        nameRow bundle pkg /\ hsame row request)
                    (fun row : BHist => hsame row request /\ UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg /\ PkgSig bundle supplyRead pkg /\
                        hsame row request /\ Cont request gate supplyRead)
                    hsame /\
                  UnaryHistory supplyRead /\ UnaryHistory bridgeRead /\
                    UnaryHistory externalityRead /\ Cont request gate supplyRead /\
                      Cont ledger nameRow bridgeRead /\
                        Cont bridgeRead provenance externalityRead /\
                          hsame ledger (append request gate) /\
                            PkgSig bundle supplyRead pkg /\ PkgSig bundle bridgeRead pkg /\
                              PkgSig bundle externalityRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateSupply supplyPkg ledgerNameBridge bridgePkg
    bridgeProvenanceExternality externalityPkg
  have supply :=
    ApophaticNameCarrier_supply_shape_noninternalization
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (supplyRead := supplyRead) (bundle := bundle) (pkg := pkg)
      carrier requestGateSupply supplyPkg
  have bridge :=
    ApophaticNameCarrier_root_bridge_counter_surface
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (bridgeRead := bridgeRead) (counterRead := externalityRead)
      (bundle := bundle) (pkg := pkg) carrier ledgerNameBridge bridgePkg
      bridgeProvenanceExternality externalityPkg
  obtain ⟨cert, _requestUnary, supplyUnary, supplyRoute, _supplyPkg⟩ := supply
  obtain ⟨bridgeUnary, externalityUnary, bridgeRoute, externalityRoute,
    ledgerSameRequestGate, _provenancePkg, bridgePkg', externalityPkg'⟩ := bridge
  exact
    ⟨cert, supplyUnary, bridgeUnary, externalityUnary, supplyRoute, bridgeRoute,
      externalityRoute, ledgerSameRequestGate, supplyPkg, bridgePkg', externalityPkg'⟩

end BEDC.Derived.ApophaticNameUp
