import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_public_normal_form_export [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      normalwordRoute downstream output : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead routes normalwordRoute ->
          Cont normalRead transports downstream ->
            Cont downstream routes output ->
              PkgSig bundle normalwordRoute pkg ->
                PkgSig bundle output pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row output ∨ hsame row normalwordRoute) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
                          hsame row normalwordRoute ∨ hsame row output)
                      (fun row : BHist =>
                        (hsame row output ∨ hsame row normalwordRoute) ∧
                          (PkgSig bundle output pkg ∧ PkgSig bundle normalwordRoute pkg))
                      hsame ∧
                    UnaryHistory normalRead ∧ UnaryHistory normalwordRoute ∧
                      UnaryHistory downstream ∧ UnaryHistory output ∧
                        Cont normal continuation normalRead ∧
                          Cont normalRead routes normalwordRoute ∧
                            Cont normalRead transports downstream ∧
                              Cont downstream routes output ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet normalReadRoute normalwordRouteRoute downstreamRoute outputRoute normalwordPkg
    outputPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalReadRoute
  have normalwordRouteUnary : UnaryHistory normalwordRoute :=
    unary_cont_closed normalReadUnary routesUnary normalwordRouteRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary downstreamRoute
  have outputUnary : UnaryHistory output :=
    unary_cont_closed downstreamUnary routesUnary outputRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row output ∨ hsame row normalwordRoute) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
              hsame row normalwordRoute ∨ hsame row output)
          (fun row : BHist =>
            (hsame row output ∨ hsame row normalwordRoute) ∧
              (PkgSig bundle output pkg ∧ PkgSig bundle normalwordRoute pkg))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro output ⟨Or.inl (hsame_refl output), outputUnary⟩
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
        constructor
        · cases source.left with
          | inl sameOutput =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameOutput)
          | inr sameNormalword =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameNormalword)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameOutput =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameOutput)))
      | inr sameNormalword =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameNormalword)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, outputPkg, normalwordPkg⟩
  }
  exact
    ⟨cert, normalReadUnary, normalwordRouteUnary, downstreamUnary, outputUnary,
      normalReadRoute, normalwordRouteRoute, downstreamRoute, outputRoute, provenancePkg⟩

end BEDC.Derived.ZnormalUp
