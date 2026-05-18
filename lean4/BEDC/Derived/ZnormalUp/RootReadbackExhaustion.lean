import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_readback_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal readback →
          PkgSig bundle readback pkg →
            SemanticNameCert
                (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                    hsame row readback)
                (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
                hsame ∧
              UnaryHistory terminalRead ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalReadback readbackPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReadback
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
          hsame := by
    exact {
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
  exact ⟨cert, terminalReadUnary, readbackUnary⟩

end BEDC.Derived.ZnormalUp
