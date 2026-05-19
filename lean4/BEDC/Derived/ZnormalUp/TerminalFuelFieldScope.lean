import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_fuel_field_scope [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          PkgSig bundle continuationRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row continuationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                    hsame row continuationRead)
                (fun row : BHist =>
                  hsame row continuationRead ∧ PkgSig bundle continuationRead pkg)
                hsame ∧
              hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                UnaryHistory continuationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead continuationReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadTerminal : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have continuationReadSource :
      (fun row : BHist => hsame row continuationRead ∧ UnaryHistory row)
        continuationRead := by
    exact ⟨hsame_refl continuationRead, continuationReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row continuationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row continuationRead)
          (fun row : BHist =>
            hsame row continuationRead ∧ PkgSig bundle continuationRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro continuationRead continuationReadSource
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
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, continuationReadPkg⟩
  }
  exact ⟨cert, terminalReadTerminal, terminalReadUnary, continuationReadUnary⟩

end BEDC.Derived.ZnormalUp
