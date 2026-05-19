import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_host_conversion_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      conversionRead hostBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead continuation conversionRead ->
          Cont conversionRead routes hostBoundary ->
            PkgSig bundle hostBoundary pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row hostBoundary ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row terminalRead ∨ hsame row conversionRead ∨
                      hsame row hostBoundary)
                  (fun row : BHist =>
                    hsame row hostBoundary ∧ PkgSig bundle hostBoundary pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ UnaryHistory conversionRead ∧
                  UnaryHistory hostBoundary ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle hostBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadContinuationConversion conversionRoutesHost
    hostBoundaryPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have conversionReadUnary : UnaryHistory conversionRead :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationConversion
  have hostBoundaryUnary : UnaryHistory hostBoundary :=
    unary_cont_closed conversionReadUnary routesUnary conversionRoutesHost
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hostBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row conversionRead ∨ hsame row hostBoundary)
          (fun row : BHist => hsame row hostBoundary ∧ PkgSig bundle hostBoundary pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hostBoundary ⟨hsame_refl hostBoundary, hostBoundaryUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, hostBoundaryPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, conversionReadUnary, hostBoundaryUnary, provenancePkg,
      hostBoundaryPkg⟩

end BEDC.Derived.ZnormalUp
