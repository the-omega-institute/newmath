import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_boundary_ledger_nonescape [AskSetup]
    [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint boundaryRead ledgerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont line boundary boundaryRead ->
        Cont boundaryRead route ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row boundaryRead ∨ hsame row ledgerRead)
                (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                hsame ∧
              UnaryHistory line ∧ UnaryHistory boundary ∧ UnaryHistory route ∧
                UnaryHistory boundaryRead ∧ UnaryHistory ledgerRead ∧
                  Cont line boundary route ∧ Cont line boundary boundaryRead ∧
                    Cont boundaryRead route ledgerRead ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet boundaryReadRoute ledgerReadRoute ledgerReadPkg
  obtain ⟨_stripUnary, _zeroUnary, lineUnary, boundaryUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, _stripZeroTransport, lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    endpointPkg⟩ := packet
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed lineUnary boundaryUnary boundaryReadRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundaryReadUnary routeUnary ledgerReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row boundaryRead ∨ hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerReadPkg⟩
  }
  exact
    ⟨cert, lineUnary, boundaryUnary, routeUnary, boundaryReadUnary, ledgerReadUnary,
      lineBoundaryRoute, boundaryReadRoute, ledgerReadRoute, endpointPkg, ledgerReadPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
