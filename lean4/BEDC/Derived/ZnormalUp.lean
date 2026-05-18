import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZnormalPacket [AskSetup] [PackageSetup]
    (typed fuel terminal normal continuation transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
    UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
          Cont continuation transports routes ∧ PkgSig bundle name pkg ∧
            PkgSig bundle provenance pkg

theorem ZnormalPacket_sibling_normalword_handoff [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      UnaryHistory normal →
        Cont normal continuation handoff →
          UnaryHistory handoff ∧ hsame handoff (append normal continuation) ∧
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet normalUnary normalContinuationHandoff
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed normalUnary continuationUnary normalContinuationHandoff
  exact ⟨handoffUnary, normalContinuationHandoff, namePkg, provenancePkg⟩

theorem ZnormalPacket_namecert_obligations [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
              bundle pkg ∧
            (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation))
        (fun _row : BHist =>
          Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
            Cont continuation transports routes ∧ PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro typed
          (And.intro packetWitness (Or.inl (hsame_refl typed)))
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
        intro row row' sameRows sourceData
        constructor
        · exact sourceData.left
        · cases sourceData.right with
          | inl sameTyped =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTyped)
          | inr rest =>
              cases rest with
              | inl sameFuel =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFuel))
              | inr rest =>
                  cases rest with
                  | inl sameTerminal =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal)))
                  | inr rest =>
                      cases rest with
                      | inl sameNormal =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameNormal))))
                      | inr sameContinuation =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (hsame_trans (hsame_symm sameRows)
                                    sameContinuation))))
    }
    pattern_sound := by
      intro _row _sourceData
      exact
        ⟨typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
          provenancePkg⟩
    ledger_sound := by
      intro row sourceData
      cases sourceData.right with
      | inl sameTyped =>
          exact And.intro (unary_transport typedUnary (hsame_symm sameTyped)) provenancePkg
      | inr rest =>
          cases rest with
          | inl sameFuel =>
              exact And.intro (unary_transport fuelUnary (hsame_symm sameFuel)) provenancePkg
          | inr rest =>
              cases rest with
              | inl sameTerminal =>
                  exact And.intro
                    (unary_transport terminalUnary (hsame_symm sameTerminal)) provenancePkg
              | inr rest =>
                  cases rest with
                  | inl sameNormal =>
                      exact And.intro
                        (unary_transport normalUnary (hsame_symm sameNormal)) provenancePkg
                  | inr sameContinuation =>
                      exact And.intro
                        (unary_transport continuationUnary (hsame_symm sameContinuation))
                        provenancePkg
  }

theorem ZnormalPacket_root_bhist_source_surface [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
        UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
          UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
            Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
              Cont continuation transports routes ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
      terminalNormalContinuation, continuationTransportsRoutes, provenancePkg⟩

theorem ZnormalPacket_normal_form_consumer_coverage [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          PkgSig bundle downstream pkg →
            SemanticNameCert
                (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont normal continuation normalRead ∧
                    Cont normalRead transports row ∧ PkgSig bundle downstream pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle downstream pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory downstream := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro downstream (And.intro (hsame_refl downstream) downstreamUnary)
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
          intro row row' sameRows sourceData
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceData.left
          · exact unary_transport sourceData.right sameRows
      }
      pattern_sound := by
        intro row sourceData
        exact
          ⟨normalContinuationRead,
            cont_result_hsame_transport normalReadTransportsDownstream
              (hsame_symm sourceData.left),
            downstreamPkg⟩
      ledger_sound := by
        intro row sourceData
        exact ⟨sourceData.right, downstreamPkg⟩
    }
  · exact ⟨normalReadUnary, downstreamUnary⟩

theorem ZnormalPacket_componentwise_namecert_transport [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name typed' fuel'
      terminal' normal' continuation' transports' routes' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      hsame typed typed' ->
        hsame fuel fuel' ->
          hsame terminal terminal' ->
            hsame normal normal' ->
              hsame continuation continuation' ->
                hsame transports transports' ->
                  hsame routes routes' ->
                    hsame provenance provenance' ->
                      hsame name name' ->
                        Cont typed' fuel' terminal' ->
                          Cont terminal' normal' continuation' ->
                            Cont continuation' transports' routes' ->
                              PkgSig bundle name' pkg ->
                                PkgSig bundle provenance' pkg ->
                                  ZnormalPacket typed' fuel' terminal' normal' continuation'
                                    transports' routes' provenance' name' bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sameTyped sameFuel sameTerminal sameNormal sameContinuation sameTransports
    sameRoutes sameProvenance sameName typedFuelTerminal' terminalNormalContinuation'
    continuationTransportsRoutes' namePkg' provenancePkg'
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have typedUnary' : UnaryHistory typed' :=
    unary_transport typedUnary sameTyped
  have fuelUnary' : UnaryHistory fuel' :=
    unary_transport fuelUnary sameFuel
  have terminalUnary' : UnaryHistory terminal' :=
    unary_transport terminalUnary sameTerminal
  have normalUnary' : UnaryHistory normal' :=
    unary_transport normalUnary sameNormal
  have continuationUnary' : UnaryHistory continuation' :=
    unary_transport continuationUnary sameContinuation
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' :=
    unary_transport nameUnary sameName
  exact
    ⟨typedUnary', fuelUnary', terminalUnary', normalUnary', continuationUnary',
      transportsUnary', routesUnary', provenanceUnary', nameUnary', typedFuelTerminal',
      terminalNormalContinuation', continuationTransportsRoutes', namePkg', provenancePkg'⟩

theorem ZnormalPacket_downstream_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name
      normalRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          PkgSig bundle downstream pkg →
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory normalRead ∧
                UnaryHistory transports ∧ UnaryHistory downstream ∧ Cont typed fuel terminal ∧
                  Cont terminal normal continuation ∧ Cont normal continuation normalRead ∧
                    Cont normalRead transports downstream ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary, normalReadUnary,
      transportsUnary, downstreamUnary, typedFuelTerminal, terminalNormalContinuation,
      normalContinuationRead, normalReadTransportsDownstream, namePkg, provenancePkg,
      downstreamPkg⟩

theorem ZnormalPacket_root_total_host_source_coverage [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name sourceRead
      sourceExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel sourceRead →
        Cont sourceRead name sourceExport →
          PkgSig bundle sourceExport pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sourceExport ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
                    hsame row sourceExport)
                (fun row : BHist => hsame row sourceExport ∧ PkgSig bundle sourceExport pkg)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory sourceExport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelSourceRead sourceReadNameSourceExport sourceExportPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelSourceRead
  have sourceExportUnary : UnaryHistory sourceExport :=
    unary_cont_closed sourceReadUnary nameUnary sourceReadNameSourceExport
  have sourceExportSource :
      (fun row : BHist => hsame row sourceExport ∧ UnaryHistory row) sourceExport := by
    exact ⟨hsame_refl sourceExport, sourceExportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
              hsame row sourceExport)
          (fun row : BHist => hsame row sourceExport ∧ PkgSig bundle sourceExport pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sourceExport sourceExportSource
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro row source
        exact ⟨source.left, sourceExportPkg⟩
    }
  exact ⟨cert, sourceReadUnary, sourceExportUnary⟩

theorem ZnormalPacket_downstream_normal_route_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          PkgSig bundle downstream pkg →
            SemanticNameCert
                (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
                    hsame row downstream)
                (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory downstream := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have downstreamSource :
      (fun row : BHist => hsame row downstream ∧ UnaryHistory row) downstream := by
    exact ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
              hsame row downstream)
          (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro downstream downstreamSource
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro row source
        exact ⟨source.left, downstreamPkg⟩
    }
  exact ⟨cert, normalReadUnary, downstreamUnary⟩

theorem ZnormalPacket_total_host_refusal_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name refusal
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal refusal →
        Cont refusal continuation readback →
          PkgSig bundle readback pkg →
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory refusal ∧ UnaryHistory continuation ∧
                UnaryHistory readback ∧ Cont typed fuel terminal ∧
                  Cont terminal normal refusal ∧ Cont refusal continuation readback ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet terminalNormalRefusal refusalContinuationReadback readbackPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRefusal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed refusalUnary continuationUnary refusalContinuationReadback
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, refusalUnary, continuationUnary,
      readbackUnary, typedFuelTerminal, terminalNormalRefusal, refusalContinuationReadback,
      provenancePkg, readbackPkg⟩

theorem ZnormalRootCarrierObligationCompletion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed terminal rootRead →
        PkgSig bundle rootRead pkg →
          UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory rootRead ∧ Cont typed fuel terminal ∧
                  Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                    Cont typed terminal rootRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet typedTerminalRootRead rootReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed typedUnary terminalUnary typedTerminalRootRead
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, rootReadUnary,
      typedFuelTerminal, terminalNormalContinuation, continuationTransportsRoutes,
      typedTerminalRootRead, namePkg, provenancePkg, rootReadPkg⟩

theorem ZnormalPacket_root_terminal_normality_determinacy [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
          Cont terminal normal continuation ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  exact
    ⟨terminalReadSame, terminalReadUnary, terminalNormalContinuation, provenancePkg⟩

theorem ZnormalRootUnblockNameCertExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                  hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                    hsame row routes ∨ hsame row rootRead)
              (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
              hsame ∧
            Cont typed fuel terminal ∧ Cont terminal normal rootRead ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalRootRead rootReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRootRead
  have rootReadSource :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                hsame row routes ∨ hsame row rootRead)
          (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootRead rootReadSource
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro row source
        exact ⟨source.left, rootReadPkg⟩
    }
  exact ⟨cert, typedFuelTerminal, terminalNormalRootRead, provenancePkg⟩

end BEDC.Derived.ZnormalUp
