import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootTotalHostReadbackTriad [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      readback nonescape : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal readback →
          Cont provenance name nonescape →
            PkgSig bundle readback pkg →
              PkgSig bundle nonescape pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                        hsame row readback)
                    (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory fuel ∧ UnaryHistory readback ∧
                    UnaryHistory nonescape ∧ Cont typed fuel terminalRead ∧
                      Cont terminalRead normal readback ∧ Cont provenance name nonescape ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg ∧
                          PkgSig bundle nonescape pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalReadback provenanceNameNonescape
    readbackPkg nonescapePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReadback
  have nonescapeUnary : UnaryHistory nonescape :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameNonescape
  have readbackSource :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row readback)
          (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback readbackSource
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
      exact ⟨source.left, readbackPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, fuelUnary, readbackUnary, nonescapeUnary,
      typedFuelTerminalRead, terminalReadNormalReadback, provenanceNameNonescape, provenancePkg,
      readbackPkg, nonescapePkg⟩

theorem ZnormalPacket_root_fuel_replay_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name replay
      exposed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont fuel routes replay →
        Cont replay terminal exposed →
          PkgSig bundle exposed pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exposed ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont fuel routes replay ∧ Cont replay terminal row ∧
                    PkgSig bundle exposed pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle exposed pkg)
                hsame ∧
              UnaryHistory replay ∧ UnaryHistory exposed := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro packet fuelRoutesReplay replayTerminalExposed exposedPkg
  obtain ⟨_typedUnary, fuelUnary, terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed fuelUnary routesUnary fuelRoutesReplay
  have exposedUnary : UnaryHistory exposed :=
    unary_cont_closed replayUnary terminalUnary replayTerminalExposed
  have exposedSource :
      (fun row : BHist => hsame row exposed ∧ UnaryHistory row) exposed := by
    exact ⟨hsame_refl exposed, exposedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exposed ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont fuel routes replay ∧ Cont replay terminal row ∧
              PkgSig bundle exposed pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle exposed pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exposed exposedSource
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
      intro row source
      exact
        ⟨fuelRoutesReplay,
          cont_result_hsame_transport replayTerminalExposed (hsame_symm source.left),
          exposedPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exposedPkg⟩
  }
  exact ⟨cert, replayUnary, exposedUnary⟩

theorem ZnormalPacket_root_total_host_readback_factorization [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          Cont downstream routes hostRead →
            PkgSig bundle hostRead pkg →
              UnaryHistory normalRead ∧ UnaryHistory downstream ∧ UnaryHistory hostRead ∧
                Cont normal continuation normalRead ∧ Cont normalRead transports downstream ∧
                  Cont downstream routes hostRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamRoutesHostRead
    hostReadPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesHostRead
  exact
    ⟨normalReadUnary, downstreamUnary, hostReadUnary, normalContinuationRead,
      normalReadTransportsDownstream, downstreamRoutesHostRead, provenancePkg, hostReadPkg⟩

end BEDC.Derived.ZnormalUp
