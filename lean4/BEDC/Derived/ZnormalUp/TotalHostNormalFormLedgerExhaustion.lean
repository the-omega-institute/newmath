import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_normal_form_ledger_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal continuationRead ->
          Cont continuationRead transports downstream ->
            PkgSig bundle downstream pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                      hsame row continuationRead ∨ hsame row downstream)
                  (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ UnaryHistory continuationRead ∧
                  UnaryHistory downstream ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    continuationReadTransportsDownstream downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row continuationRead ∨ hsame row downstream)
          (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro downstream ⟨hsame_refl downstream, downstreamUnary⟩
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
      exact ⟨source.left, downstreamPkg⟩
  }
  exact ⟨cert, terminalReadSame, continuationReadUnary, downstreamUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
