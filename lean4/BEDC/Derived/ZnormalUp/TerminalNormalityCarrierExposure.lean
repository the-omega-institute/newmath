import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_normality_carrier_exposure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal continuationRead ->
          Cont normal continuation siblingRead ->
            PkgSig bundle continuationRead pkg ->
              PkgSig bundle siblingRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                        hsame row continuationRead)
                    (fun row : BHist =>
                      hsame row terminalRead ∧ PkgSig bundle continuationRead pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory continuationRead ∧
                    UnaryHistory siblingRead ∧ hsame siblingRead (append normal continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    normalContinuationSiblingRead continuationReadPkg _siblingReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row continuationRead)
          (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle continuationRead pkg)
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, continuationReadPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, continuationReadUnary, siblingReadUnary,
      normalContinuationSiblingRead⟩

end BEDC.Derived.ZnormalUp
