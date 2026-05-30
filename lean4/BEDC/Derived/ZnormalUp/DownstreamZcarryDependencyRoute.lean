import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_downstream_zcarry_dependency_route [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream zcarryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead transports downstream ->
          Cont downstream routes zcarryRead ->
            PkgSig bundle zcarryRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row zcarryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row normal ∨ hsame row downstream ∨ hsame row zcarryRead)
                  (fun row : BHist => hsame row zcarryRead ∧ PkgSig bundle zcarryRead pkg)
                  hsame ∧
                UnaryHistory normalRead ∧ UnaryHistory downstream ∧
                  UnaryHistory zcarryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamRoutesZcarry
    zcarryPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have zcarryUnary : UnaryHistory zcarryRead :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesZcarry
  have zcarrySource :
      (fun row : BHist => hsame row zcarryRead ∧ UnaryHistory row) zcarryRead := by
    exact ⟨hsame_refl zcarryRead, zcarryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zcarryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row downstream ∨ hsame row zcarryRead)
          (fun row : BHist => hsame row zcarryRead ∧ PkgSig bundle zcarryRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro zcarryRead zcarrySource
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, zcarryPkg⟩
    }
  exact ⟨cert, normalReadUnary, downstreamUnary, zcarryUnary⟩

end BEDC.Derived.ZnormalUp
