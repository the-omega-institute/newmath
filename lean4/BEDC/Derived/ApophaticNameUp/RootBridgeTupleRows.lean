import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_request_image_row [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow imageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request imageRead →
        PkgSig bundle imageRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row request)
              (fun row : BHist => hsame row request ∧ UnaryHistory row)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle imageRead pkg ∧
                  Cont socket request imageRead)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory imageRead ∧
              Cont socket request imageRead ∧ hsame ledger (append request gate) ∧
                PkgSig bundle imageRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestImage imagePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed socketUnary requestUnary socketRequestImage
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row request)
          (fun row : BHist => hsame row request ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle imageRead pkg ∧
              Cont socket request imageRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro request ⟨carrierPacket, hsame_refl request⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport requestUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, imagePkg, socketRequestImage⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, imageUnary, socketRequestImage,
      ledgerSameRequestGate, imagePkg⟩

theorem ApophaticNameCarrier_root_bridge_tuple_ledger [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow downstreamRead ->
        Cont downstreamRead route handoff ->
          PkgSig bundle handoff pkg ->
            UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧ UnaryHistory handoff ∧
              hsame ledger (append request gate) ∧ Cont ledger nameRow downstreamRead ∧
                Cont downstreamRead route handoff ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier ledgerNameRowDownstream downstreamRouteHandoff handoffPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRowDownstream
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed downstreamUnary routeUnary downstreamRouteHandoff
  exact
    ⟨ledgerUnary, downstreamUnary, handoffUnary, ledgerSameRequestGate,
      ledgerNameRowDownstream, downstreamRouteHandoff, provenancePkg, handoffPkg⟩

theorem ApophaticNameCarrier_root_bridge_tuple_terminal_exhaustion
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead handoffRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow downstreamRead ->
        Cont downstreamRead route handoffRead ->
          PkgSig bundle handoffRead pkg ->
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧ UnaryHistory handoffRead ∧
                Cont socket request gate ∧ Cont ledger nameRow downstreamRead ∧
                  Cont downstreamRead route handoffRead ∧ hsame ledger (append request gate) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier ledgerNameRowDownstream downstreamRouteHandoff handoffPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRowDownstream
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed downstreamUnary routeUnary downstreamRouteHandoff
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, downstreamUnary, handoffUnary,
      socketRequestGate, ledgerNameRowDownstream, downstreamRouteHandoff,
      ledgerSameRequestGate, provenancePkg, handoffPkg⟩

theorem ApophaticNameCarrier_classifier_stability [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      hsame provenance transported →
        PkgSig bundle transported pkg →
          SemanticNameCert
            (fun row : BHist =>
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg ∧ hsame row transported)
            (fun row : BHist => hsame row transported ∧ UnaryHistory row)
            (fun row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle transported pkg ∧
                hsame row transported)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier provenanceTransported transportedPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro transported (And.intro carrierPacket (hsame_refl transported))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left
          (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      have provenanceRow : hsame provenance row :=
        hsame_trans provenanceTransported (hsame_symm source.right)
      exact And.intro source.right (unary_transport provenanceUnary provenanceRow)
    ledger_sound := by
      intro row source
      exact And.intro provenancePkg (And.intro transportedPkg source.right)
  }

theorem ApophaticNameCarrier_boundary_request_tuple_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow imageRead readbackRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request imageRead →
        Cont ledger nameRow readbackRead →
          PkgSig bundle imageRead pkg →
            PkgSig bundle readbackRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row request)
                  (fun row : BHist =>
                    hsame row request ∧ UnaryHistory row ∧ Cont socket request imageRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle readbackRead pkg ∧
                      hsame row request ∧ Cont ledger nameRow readbackRead)
                  hsame ∧
                UnaryHistory imageRead ∧ UnaryHistory readbackRead ∧
                  hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestImage ledgerNameReadback _imagePkg readbackPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed socketUnary requestUnary socketRequestImage
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameReadback
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row request)
          (fun row : BHist =>
            hsame row request ∧ UnaryHistory row ∧ Cont socket request imageRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle readbackRead pkg ∧
              hsame row request ∧ Cont ledger nameRow readbackRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro request ⟨carrierPacket, hsame_refl request⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport requestUnary (hsame_symm source.right),
            socketRequestImage⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, readbackPkg, source.right, ledgerNameReadback⟩
    }
  exact ⟨cert, imageUnary, readbackUnary, ledgerSameRequestGate⟩

theorem ApophaticNameCarrier_root_bridge_tuple_visible_request_factorization
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow visibleRead bridgeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate visibleRead →
        Cont visibleRead provenance bridgeRead →
          PkgSig bundle bridgeRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧
                    hsame row visibleRead)
                (fun row : BHist =>
                  hsame row visibleRead ∧ UnaryHistory row ∧ Cont request gate visibleRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
                    hsame row visibleRead)
                hsame ∧
              UnaryHistory visibleRead ∧ UnaryHistory bridgeRead ∧
              Cont request gate visibleRead ∧ Cont visibleRead provenance bridgeRead ∧
              hsame ledger (append request gate) ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateVisible visibleProvenanceBridge bridgePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary, _routeUnary,
    provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have visibleUnary : UnaryHistory visibleRead :=
    unary_cont_closed requestUnary gateUnary requestGateVisible
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed visibleUnary provenanceUnary visibleProvenanceBridge
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg ∧
              hsame row visibleRead)
          (fun row : BHist =>
            hsame row visibleRead ∧ UnaryHistory row ∧ Cont request gate visibleRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
              hsame row visibleRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro visibleRead ⟨carrierPacket, hsame_refl visibleRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport visibleUnary (hsame_symm source.right),
            requestGateVisible⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, bridgePkg, source.right⟩
    }
  exact
    ⟨cert, visibleUnary, bridgeUnary, requestGateVisible, visibleProvenanceBridge,
      ledgerSameRequestGate, provenancePkg, bridgePkg⟩

theorem ApophaticNameCarrier_ledger_refusal_transport_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow transportedLedger auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      hsame ledger transportedLedger →
        Cont transportedLedger nameRow auditRead →
          PkgSig bundle auditRead pkg →
            UnaryHistory ledger ∧ UnaryHistory transportedLedger ∧ UnaryHistory auditRead ∧
              hsame transportedLedger (append request gate) ∧
                Cont transportedLedger nameRow auditRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier ledgerTransport ledgerNameAudit auditPkg
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  cases ledgerTransport
  have transportedUnary : UnaryHistory ledger := ledgerUnary
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameAudit
  exact
    ⟨ledgerUnary, transportedUnary, auditUnary, ledgerSameRequestGate, ledgerNameAudit,
      provenancePkg, auditPkg⟩

theorem ApophaticNameCarrier_closure_refusal_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow exported auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont ledger route exported →
        Cont ledger nameRow auditRead →
          PkgSig bundle exported pkg →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row nameRow ∧
                      ApophaticNameCarrier socket request gate ledger transport route provenance
                        nameRow bundle pkg)
                  (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg ∧
                      PkgSig bundle auditRead pkg)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                  UnaryHistory ledger ∧ UnaryHistory exported ∧ UnaryHistory auditRead ∧
                    Cont socket request gate ∧ Cont ledger route exported ∧
                      Cont ledger nameRow auditRead ∧ hsame ledger (append request gate) ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerRouteExported ledgerNameAudit exportedPkg auditPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteExported
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameRow ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg ∧
              PkgSig bundle auditRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro nameRow ⟨hsame_refl nameRow, carrierPacket⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, unary_transport nameRowUnary (hsame_symm source.left)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, exportedPkg, auditPkg⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, exportedUnary, auditUnary,
      socketRequestGate, ledgerRouteExported, ledgerNameAudit, ledgerSameRequestGate,
      provenancePkg⟩

theorem ApophaticNameCarrier_kernel_scope_triad [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont socket request gate ->
        Cont gate ledger nameRow ->
          Cont ledger nameRow kernelRead ->
            PkgSig bundle provenance pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row gate)
                  (fun row : BHist =>
                    hsame row gate ∧ UnaryHistory row ∧ Cont socket request gate)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ Cont gate ledger nameRow ∧
                      Cont ledger nameRow kernelRead)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                  UnaryHistory kernelRead ∧ hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestGate' gateLedgerNameRow' ledgerNameKernel provenancePkg'
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameKernel
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row gate)
          (fun row : BHist => hsame row gate ∧ UnaryHistory row ∧ Cont socket request gate)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ Cont gate ledger nameRow ∧
              Cont ledger nameRow kernelRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro gate ⟨carrierPacket, hsame_refl gate⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport gateUnary (hsame_symm source.right),
            socketRequestGate'⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg', gateLedgerNameRow', ledgerNameKernel⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, kernelUnary, ledgerSameRequestGate⟩

theorem ApophaticNameCarrier_downstream_refusal_replay [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger nameRow downstreamRead ->
        Cont downstreamRead route replayRead ->
          PkgSig bundle replayRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row downstreamRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ UnaryHistory row ∧
                    Cont ledger nameRow downstreamRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg ∧
                    hsame row downstreamRead ∧ Cont downstreamRead route replayRead)
                hsame ∧
              UnaryHistory downstreamRead ∧ UnaryHistory replayRead ∧
                Cont ledger nameRow downstreamRead ∧
                  Cont downstreamRead route replayRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameDownstream downstreamRouteReplay replayPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed downstreamUnary routeUnary downstreamRouteReplay
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row downstreamRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ UnaryHistory row ∧
              Cont ledger nameRow downstreamRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg ∧
              hsame row downstreamRead ∧ Cont downstreamRead route replayRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro downstreamRead ⟨carrierPacket, hsame_refl downstreamRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport downstreamUnary (hsame_symm source.right),
            ledgerNameDownstream⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, replayPkg, source.right, downstreamRouteReplay⟩
    }
  exact
    ⟨cert, downstreamUnary, replayUnary, ledgerNameDownstream, downstreamRouteReplay,
      provenancePkg⟩

end BEDC.Derived.ApophaticNameUp
