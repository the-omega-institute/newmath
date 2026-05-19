import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservationCouplingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObservationCouplingCarrier [AskSetup] [PackageSetup]
    (histA histB routeA routeB transport replay ledger provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  UnaryHistory histA ∧ UnaryHistory histB ∧ UnaryHistory routeA ∧ UnaryHistory routeB ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont histA routeA transport ∧
        Cont histB routeB replay ∧ Cont transport replay localName ∧ hsame ledger localName ∧
          Cont ledger provenance localName ∧ PkgSig bundle provenance pkg

theorem ObservationCouplingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {histA histB routeA routeB transport replay ledger provenance localName readA readB
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg ->
      Cont histA routeA readA ->
        Cont histB routeB readB ->
          Cont readA readB ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    ObservationCouplingCarrier histA histB routeA routeB transport replay ledger
                      provenance localName bundle pkg ∧ hsame row localName)
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                      hsame row localName)
                  hsame ∧
                UnaryHistory readA ∧ UnaryHistory readB ∧ UnaryHistory ledgerRead ∧
                  Cont histA routeA readA ∧ Cont histB routeB readB ∧
                    Cont readA readB ledgerRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier histRouteReadA histRouteReadB readsLedger ledgerPkg
  have carrierFull :
      ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg :=
    carrier
  obtain ⟨histAUnary, histBUnary, routeAUnary, routeBUnary, _transportUnary, _replayUnary,
    _ledgerUnary, _provenanceUnary, localNameUnary, histATransport, histBReplay,
    transportReplayLocal, _ledgerSameLocal, _ledgerProvenanceLocal, provenancePkg⟩ := carrier
  have readAUnary : UnaryHistory readA :=
    unary_cont_closed histAUnary routeAUnary histRouteReadA
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed histBUnary routeBUnary histRouteReadB
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed readAUnary readBUnary readsLedger
  have readATransportSame : hsame readA transport :=
    cont_deterministic histRouteReadA histATransport
  have readBReplaySame : hsame readB replay :=
    cont_deterministic histRouteReadB histBReplay
  have ledgerReadLocalSame : hsame ledgerRead localName :=
    cont_respects_hsame readATransportSame readBReplaySame readsLedger transportReplayLocal
  have sourceLocal :
      ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
          localName bundle pkg ∧ hsame localName localName :=
    ⟨carrierFull, hsame_refl localName⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ObservationCouplingCarrier histA histB routeA routeB transport replay ledger
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧ hsame row localName)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      have rowLedgerRead : hsame row ledgerRead :=
        hsame_trans source.right (hsame_symm ledgerReadLocalSame)
      have rowUnary : UnaryHistory row :=
        unary_transport localNameUnary (hsame_symm source.right)
      exact ⟨rowLedgerRead, rowUnary⟩
    ledger_sound := by
      intro row source
      exact ⟨provenancePkg, ledgerPkg, source.right⟩
  }
  exact
    ⟨cert, readAUnary, readBUnary, ledgerReadUnary, histRouteReadA, histRouteReadB,
      readsLedger, provenancePkg, ledgerPkg⟩

theorem ObservationCouplingCarrier_symmetric_rate_boundary [AskSetup] [PackageSetup]
    {histA histB routeA routeB transport replay ledger provenance localName readA readB
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg ->
      Cont histA routeA readA ->
        Cont histB routeB readB ->
          Cont readA readB ledgerRead ->
            hsame ledgerRead ledger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier histRouteReadA histRouteReadB readsLedger
  obtain ⟨_histAUnary, _histBUnary, _routeAUnary, _routeBUnary, _transportUnary,
    _replayUnary, _ledgerUnary, _provenanceUnary, _localNameUnary, histATransport,
    histBReplay, transportReplayLocal, ledgerSameLocal, _ledgerProvenanceLocal,
    _provenancePkg⟩ := carrier
  have readATransportSame : hsame readA transport :=
    cont_deterministic histRouteReadA histATransport
  have readBReplaySame : hsame readB replay :=
    cont_deterministic histRouteReadB histBReplay
  have ledgerReadLocalSame : hsame ledgerRead localName :=
    cont_respects_hsame readATransportSame readBReplaySame readsLedger transportReplayLocal
  exact hsame_trans ledgerReadLocalSame (hsame_symm ledgerSameLocal)

theorem ObservationCouplingCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {histA histB routeA routeB transport replay ledger provenance localName readA readB ledgerRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg ->
      Cont histA routeA readA ->
        Cont histB routeB readB ->
          Cont readA readB ledgerRead ->
            Cont ledgerRead provenance downstream ->
              PkgSig bundle downstream pkg ->
                hsame ledgerRead ledger ∧ UnaryHistory downstream ∧
                  Cont ledgerRead provenance downstream ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier histRouteReadA histRouteReadB readsLedger ledgerReadProvenanceDownstream
    downstreamPkg
  obtain ⟨histAUnary, histBUnary, routeAUnary, routeBUnary, _transportUnary, _replayUnary,
    _ledgerUnary, provenanceUnary, _localNameUnary, histATransport, histBReplay,
    transportReplayLocal, ledgerSameLocal, _ledgerProvenanceLocal, _provenancePkg⟩ := carrier
  have readAUnary : UnaryHistory readA :=
    unary_cont_closed histAUnary routeAUnary histRouteReadA
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed histBUnary routeBUnary histRouteReadB
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed readAUnary readBUnary readsLedger
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed ledgerReadUnary provenanceUnary ledgerReadProvenanceDownstream
  have readATransportSame : hsame readA transport :=
    cont_deterministic histRouteReadA histATransport
  have readBReplaySame : hsame readB replay :=
    cont_deterministic histRouteReadB histBReplay
  have ledgerReadLocalSame : hsame ledgerRead localName :=
    cont_respects_hsame readATransportSame readBReplaySame readsLedger transportReplayLocal
  have ledgerReadLedgerSame : hsame ledgerRead ledger :=
    hsame_trans ledgerReadLocalSame (hsame_symm ledgerSameLocal)
  exact
    ⟨ledgerReadLedgerSame, downstreamUnary, ledgerReadProvenanceDownstream, downstreamPkg⟩

theorem ObservationCouplingCarrier_locality_obligations [AskSetup] [PackageSetup]
    {histA histB routeA routeB transport replay ledger provenance localName readA readB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg ->
      Cont histA routeA readA ->
        Cont histB routeB readB ->
          UnaryHistory histA ∧ UnaryHistory histB ∧ UnaryHistory readA ∧
            UnaryHistory readB ∧ Cont histA routeA readA ∧ Cont histB routeB readB ∧
              hsame readA transport ∧ hsame readB replay ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier histRouteReadA histRouteReadB
  rcases carrier with
    ⟨histAUnary, histBUnary, routeAUnary, routeBUnary, _transportUnary, _replayUnary,
      _ledgerUnary, _provenanceUnary, _localNameUnary, histATransport, histBReplay,
      _transportReplayLocal, _ledgerSameLocal, _ledgerProvenanceLocal, provenancePkg⟩
  have readAUnary : UnaryHistory readA :=
    unary_cont_closed histAUnary routeAUnary histRouteReadA
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed histBUnary routeBUnary histRouteReadB
  have readATransportSame : hsame readA transport :=
    cont_deterministic histRouteReadA histATransport
  have readBReplaySame : hsame readB replay :=
    cont_deterministic histRouteReadB histBReplay
  exact
    ⟨histAUnary, histBUnary, readAUnary, readBUnary, histRouteReadA, histRouteReadB,
      readATransportSame, readBReplaySame, provenancePkg⟩

theorem ObservationCouplingCarrier_standard_bridge_boundary [AskSetup] [PackageSetup]
    {histA histB routeA routeB transport replay ledger provenance localName readA readB
      ledgerRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg ->
      Cont histA routeA readA ->
        Cont histB routeB readB ->
          Cont readA readB ledgerRead ->
            Cont ledgerRead localName bridgeRead ->
              PkgSig bundle bridgeRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row readA ∨ hsame row readB ∨ hsame row ledgerRead ∨
                        hsame row bridgeRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
                        hsame row bridgeRead)
                    hsame ∧
                  UnaryHistory readA ∧ UnaryHistory readB ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory bridgeRead ∧ hsame ledgerRead ledger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier histRouteReadA histRouteReadB readsLedger ledgerLocalBridge bridgePkg
  have carrierFull :
      ObservationCouplingCarrier histA histB routeA routeB transport replay ledger provenance
        localName bundle pkg :=
    carrier
  obtain ⟨histAUnary, histBUnary, routeAUnary, routeBUnary, _transportUnary, _replayUnary,
    _ledgerUnary, _provenanceUnary, localNameUnary, _histATransport, _histBReplay,
    _transportReplayLocal, _ledgerSameLocal, _ledgerProvenanceLocal, provenancePkg⟩ := carrier
  have readAUnary : UnaryHistory readA :=
    unary_cont_closed histAUnary routeAUnary histRouteReadA
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed histBUnary routeBUnary histRouteReadB
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed readAUnary readBUnary readsLedger
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed ledgerReadUnary localNameUnary ledgerLocalBridge
  have ledgerReadSameLedger : hsame ledgerRead ledger :=
    ObservationCouplingCarrier_symmetric_rate_boundary carrierFull histRouteReadA histRouteReadB
      readsLedger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readA ∨ hsame row readB ∨ hsame row ledgerRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
              hsame row bridgeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, bridgePkg, source.left⟩
  }
  exact
    ⟨cert, readAUnary, readBUnary, ledgerReadUnary, bridgeReadUnary, ledgerReadSameLedger⟩

end BEDC.Derived.ObservationCouplingUp
