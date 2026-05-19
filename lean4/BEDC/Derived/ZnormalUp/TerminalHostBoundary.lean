import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_host_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute siblingRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal terminalRoute ->
          Cont normal continuation siblingRead ->
            Cont siblingRead transports publicRead ->
              PkgSig bundle terminalRoute pkg ->
                PkgSig bundle siblingRead pkg ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row terminalRead ∨ hsame row terminalRoute ∨
                            hsame row siblingRead ∨ hsame row publicRead)
                        (fun row : BHist =>
                          hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                        hsame ∧
                      hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
                        UnaryHistory siblingRead ∧ UnaryHistory publicRead ∧
                          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRoute normalContinuationSibling
    siblingTransportsPublic _terminalRoutePkg _siblingReadPkg publicReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
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
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed siblingReadUnary transportsUnary siblingTransportsPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row terminalRoute ∨
              hsame row siblingRead ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact ⟨source.left, publicReadPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, terminalRouteSame, siblingReadUnary, publicReadUnary,
      provenancePkg⟩

end BEDC.Derived.ZnormalUp
