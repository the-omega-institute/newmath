import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_namecert_terminal_route_readiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead terminalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          Cont continuationRead transports terminalRoute →
            PkgSig bundle terminalRoute pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRoute ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont typed fuel terminalRead ∧
                      Cont terminalRead normal continuationRead ∧
                        Cont continuationRead transports row ∧ PkgSig bundle terminalRoute pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRoute pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                  UnaryHistory continuationRead ∧ UnaryHistory terminalRoute ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    continuationReadTransportsTerminalRoute terminalRoutePkg
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
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsTerminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont typed fuel terminalRead ∧
              Cont terminalRead normal continuationRead ∧
                Cont continuationRead transports row ∧ PkgSig bundle terminalRoute pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRoute pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro terminalRoute ⟨hsame_refl terminalRoute, terminalRouteUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨typedFuelTerminalRead, terminalReadNormalContinuationRead,
            cont_result_hsame_transport continuationReadTransportsTerminalRoute
              (hsame_symm source.left),
            terminalRoutePkg⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right, terminalRoutePkg⟩
    }
  exact
    ⟨cert, terminalReadSame, terminalReadUnary, continuationReadUnary,
      terminalRouteUnary, provenancePkg, terminalRoutePkg⟩

end BEDC.Derived.ZnormalUp
