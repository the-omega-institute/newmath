import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootFuelRouteNonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name fuelRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel fuelRead →
        Cont fuelRead terminal terminalRead →
          PkgSig bundle terminalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row fuelRead ∨
                    hsame row terminalRead)
                (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                hsame ∧
              UnaryHistory fuelRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelRead fuelReadTerminalRead terminalReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have fuelReadUnary : UnaryHistory fuelRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed fuelReadUnary terminalUnary fuelReadTerminalRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row fuelRead ∨
              hsame row terminalRead)
          (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalReadUnary⟩
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
      exact ⟨source.left, terminalReadPkg⟩
  }
  exact ⟨cert, fuelReadUnary, terminalReadUnary⟩

end BEDC.Derived.ZnormalUp
