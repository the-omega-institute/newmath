import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootDownstreamNormalFormReadiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal normalRead ->
          Cont normalRead transports downstream ->
            PkgSig bundle downstream pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row normalRead ∨
                      hsame row downstream)
                  (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ UnaryHistory normalRead ∧
                  UnaryHistory downstream ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadTransportsDownstream
    downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have downstreamSource :
      (fun row : BHist => hsame row downstream ∧ UnaryHistory row) downstream := by
    exact ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row normalRead ∨
              hsame row downstream)
          (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro downstream downstreamSource
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
        exact ⟨source.left, downstreamPkg⟩
    }
  exact
    ⟨cert, terminalReadSame, normalReadUnary, downstreamUnary, provenancePkg,
      downstreamPkg⟩

end BEDC.Derived.ZnormalUp
