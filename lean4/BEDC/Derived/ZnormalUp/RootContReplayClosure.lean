import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootContReplayClosure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name replayRead
      replayExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont continuation transports replayRead →
        Cont replayRead name replayExport →
          PkgSig bundle replayExport pkg →
            SemanticNameCert
                (fun row : BHist => hsame row replayExport ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row continuation ∨ hsame row transports ∨ hsame row replayRead ∨
                    hsame row replayExport)
                (fun row : BHist => PkgSig bundle replayExport pkg ∧ hsame row replayExport)
                hsame ∧
              UnaryHistory replayRead ∧ UnaryHistory replayExport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet continuationTransportsReplay replayNameExport replayExportPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed continuationUnary transportsUnary continuationTransportsReplay
  have replayExportUnary : UnaryHistory replayExport :=
    unary_cont_closed replayReadUnary nameUnary replayNameExport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row continuation ∨ hsame row transports ∨ hsame row replayRead ∨
              hsame row replayExport)
          (fun row : BHist => PkgSig bundle replayExport pkg ∧ hsame row replayExport)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro replayExport ⟨hsame_refl replayExport, replayExportUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨replayExportPkg, source.left⟩
    }
  exact ⟨cert, replayReadUnary, replayExportUnary⟩

theorem ZnormalPacket_fuel_replay_root_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          Cont continuationRead transports replayRead →
            PkgSig bundle replayRead pkg →
              UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminalRead ∧
                UnaryHistory normal ∧ UnaryHistory continuationRead ∧
                  UnaryHistory transports ∧ UnaryHistory replayRead ∧
                    hsame terminalRead terminal ∧ Cont terminalRead normal continuationRead ∧
                      Cont continuationRead transports replayRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    continuationReadTransportsReplay replayPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsReplay
  exact
    ⟨typedUnary, fuelUnary, terminalReadUnary, normalUnary, continuationReadUnary,
      transportsUnary, replayReadUnary, terminalReadSame, terminalReadNormalContinuationRead,
      continuationReadTransportsReplay, provenancePkg, replayPkg⟩

end BEDC.Derived.ZnormalUp
