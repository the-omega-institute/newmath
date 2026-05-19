import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootTotalHostFuelFrontier [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead fuelRead
      frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal fuelRead →
          Cont fuelRead routes frontier →
            PkgSig bundle frontier pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                      hsame row fuelRead ∨ hsame row frontier)
                  (fun row : BHist => hsame row frontier ∧ PkgSig bundle frontier pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ UnaryHistory fuelRead ∧
                  UnaryHistory frontier ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet typedFuelTerminalRead terminalReadNormalFuelRead fuelReadRoutesFrontier
    frontierPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have fuelReadUnary : UnaryHistory fuelRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalFuelRead
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed fuelReadUnary routesUnary fuelReadRoutesFrontier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row fuelRead ∨ hsame row frontier)
          (fun row : BHist => hsame row frontier ∧ PkgSig bundle frontier pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontier ⟨hsame_refl frontier, frontierUnary⟩
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
      exact ⟨source.left, frontierPkg⟩
  }
  exact ⟨cert, terminalReadSame, fuelReadUnary, frontierUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
