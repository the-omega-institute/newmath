import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_readback_route_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      readback exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal readback →
          Cont readback transports exported →
            PkgSig bundle exported pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row exported ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row terminalRead ∨ hsame row readback ∨ hsame row exported)
                  (fun row : BHist => hsame row exported ∧ PkgSig bundle exported pkg)
                  hsame ∧
                UnaryHistory terminalRead ∧ UnaryHistory readback ∧
                  UnaryHistory exported := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet typedFuelTerminalRead terminalReadNormalReadback readbackTransportsExported
    exportedPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReadback
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed readbackUnary transportsUnary readbackTransportsExported
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row readback ∨ hsame row exported)
          (fun row : BHist => hsame row exported ∧ PkgSig bundle exported pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary⟩
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
        intro _row _row' sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, exportedPkg⟩
  }
  exact ⟨cert, terminalReadUnary, readbackUnary, exportedUnary⟩

end BEDC.Derived.ZnormalUp
