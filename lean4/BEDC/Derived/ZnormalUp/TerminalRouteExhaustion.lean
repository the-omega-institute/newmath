import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_route_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal terminalRoute ->
          PkgSig bundle terminalRoute pkg ->
            hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
              UnaryHistory terminalRead ∧ UnaryHistory terminalRoute ∧
                Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalRoute terminalRoutePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalRoute
      terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRoute
  exact
    ⟨terminalReadSame, terminalRouteSame, terminalReadUnary, terminalRouteUnary,
      terminalNormalContinuation, continuationTransportsRoutes, provenancePkg,
      terminalRoutePkg⟩

theorem ZnormalPacket_root_terminal_host_route_classifier_exhaustion
    [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal routeRead →
          PkgSig bundle routeRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                    hsame row normal ∨ hsame row routeRead)
                (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
                hsame ∧
              hsame terminalRead terminal ∧ UnaryHistory routeRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet typedFuelTerminalRead terminalReadNormalRoute routePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row normal ∨ hsame row routeRead)
          (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro routeRead ⟨hsame_refl routeRead, routeReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, routePkg⟩
    }
  exact ⟨cert, terminalReadSame, routeReadUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
