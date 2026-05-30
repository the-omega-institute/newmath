import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_refusal_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead transports downstream ->
          PkgSig bundle downstream pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                    hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
                      hsame row downstream)
                (fun row : BHist => hsame row downstream ∧ PkgSig bundle downstream pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory downstream ∧ PkgSig bundle name pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
                hsame row downstream)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamPkg⟩
  }
  exact ⟨cert, normalReadUnary, downstreamUnary, namePkg, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ZnormalUp
