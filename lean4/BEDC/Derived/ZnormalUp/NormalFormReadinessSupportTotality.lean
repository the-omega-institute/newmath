import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalNormalFormReadinessSupportTotality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute normalRead downstream support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal terminalRoute ->
          Cont normal continuation normalRead ->
            Cont normalRead transports downstream ->
              Cont downstream routes support ->
                PkgSig bundle support pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row support ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row terminalRead ∨ hsame row terminalRoute ∨
                          hsame row normalRead ∨ hsame row downstream ∨ hsame row support)
                      (fun row : BHist =>
                        hsame row support ∧ PkgSig bundle support pkg)
                      hsame ∧
                    hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
                      UnaryHistory terminalRead ∧ UnaryHistory terminalRoute ∧
                        UnaryHistory normalRead ∧ UnaryHistory downstream ∧
                          UnaryHistory support ∧ Cont typed fuel terminalRead ∧
                            Cont terminalRead normal terminalRoute ∧
                              Cont normal continuation normalRead ∧
                                Cont normalRead transports downstream ∧
                                  Cont downstream routes support ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle support pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalTerminalRoute
    normalContinuationNormalRead normalReadTransportsDownstream downstreamRoutesSupport
    supportPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalTerminalRoute terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTerminalRoute
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have supportUnary : UnaryHistory support :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesSupport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row support ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row terminalRoute ∨ hsame row normalRead ∨
              hsame row downstream ∨ hsame row support)
          (fun row : BHist => hsame row support ∧ PkgSig bundle support pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro support ⟨hsame_refl support, supportUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, supportPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, terminalRouteSame, terminalReadUnary, terminalRouteUnary,
      normalReadUnary, downstreamUnary, supportUnary, typedFuelTerminalRead,
      terminalReadNormalTerminalRoute, normalContinuationNormalRead,
      normalReadTransportsDownstream, downstreamRoutesSupport, provenancePkg, supportPkg⟩

theorem ZnormalPacket_fuel_replay_exactness_certificate [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          Cont continuationRead transports replayRead →
            PkgSig bundle replayRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                      hsame row continuationRead ∨ hsame row replayRead)
                  (fun row : BHist => hsame row replayRead ∧ PkgSig bundle replayRead pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ hsame continuationRead continuation ∧
                  UnaryHistory terminalRead ∧ UnaryHistory continuationRead ∧
                    UnaryHistory replayRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    continuationReadTransportsReplayRead replayReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have continuationReadSame : hsame continuationRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalContinuationRead terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsReplayRead
  have replayReadSource :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row continuationRead ∨ hsame row replayRead)
          (fun row : BHist => hsame row replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro replayRead replayReadSource
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro row source
        exact ⟨source.left, replayReadPkg⟩
    }
  exact
    ⟨cert, terminalReadSame, continuationReadSame, terminalReadUnary,
      continuationReadUnary, replayReadUnary, provenancePkg, replayReadPkg⟩

theorem ZnormalPacket_downstream_readiness_namecert [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead downstream consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont normal continuation normalRead →
          Cont normalRead transports downstream →
            Cont downstream routes consumer →
              PkgSig bundle consumer pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row normalRead ∨
                        hsame row downstream ∨ hsame row consumer)
                    (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory normalRead ∧
                    UnaryHistory downstream ∧ UnaryHistory consumer ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead normalContinuationNormalRead
    normalReadTransportsDownstream downstreamRoutesConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have _terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  have consumerSource :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row normalRead ∨ hsame row downstream ∨
              hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer consumerSource
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
        exact ⟨source.left, consumerPkg⟩
    }
  exact
    ⟨cert, terminalReadSame, normalReadUnary, downstreamUnary, consumerUnary,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp
