import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalRouteFieldExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalRoute →
          Cont terminalRoute transports routeRead →
            PkgSig bundle routeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                      hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                        hsame row routeRead)
                  (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
                  UnaryHistory routeRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet typedFuelTerminalRead terminalReadNormalRoute routeTransportsRead routeReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
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
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed terminalRouteUnary transportsUnary routeTransportsRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                hsame row routeRead)
          (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeRead ⟨hsame_refl routeRead, routeReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeReadPkg⟩
  }
  exact ⟨cert, terminalReadSame, terminalRouteSame, routeReadUnary, provenancePkg⟩

theorem ZnormalTotalHostRefusalReadback [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalwordRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont normal continuation normalwordRead →
          Cont normalwordRead transports refusalRead →
            PkgSig bundle refusalRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row normalwordRead ∨
                      hsame row refusalRead)
                  (fun row : BHist => hsame row refusalRead ∧ PkgSig bundle refusalRead pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ UnaryHistory normalwordRead ∧
                  UnaryHistory refusalRead ∧ Cont normal continuation normalwordRead ∧
                    Cont normalwordRead transports refusalRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet typedFuelTerminalRead normalContinuationRead normalwordTransportsRefusal
    refusalReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have normalwordReadUnary : UnaryHistory normalwordRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed normalwordReadUnary transportsUnary normalwordTransportsRefusal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row normalwordRead ∨
              hsame row refusalRead)
          (fun row : BHist => hsame row refusalRead ∧ PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalReadUnary⟩
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
      exact ⟨source.left, refusalReadPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, normalwordReadUnary, refusalReadUnary,
      normalContinuationRead, normalwordTransportsRefusal, provenancePkg, refusalReadPkg⟩

end BEDC.Derived.ZnormalUp
