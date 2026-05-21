import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_witness_scope_binding [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint sourceRead lineRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont strip zero sourceRead ->
        Cont sourceRead line lineRead ->
          Cont line boundary boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sourceRead ∨ hsame row lineRead ∨ hsame row boundaryRead)
                  (fun row : BHist => hsame row boundaryRead ∧ PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory strip ∧ UnaryHistory zero ∧ UnaryHistory line ∧
                  UnaryHistory boundary ∧ UnaryHistory sourceRead ∧ UnaryHistory lineRead ∧
                    UnaryHistory boundaryRead ∧ Cont strip zero transport ∧
                      Cont strip zero sourceRead ∧ Cont sourceRead line lineRead ∧
                        Cont line boundary route ∧ Cont line boundary boundaryRead ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceReadRoute lineReadRoute boundaryReadRoute boundaryReadPkg
  obtain ⟨stripUnary, zeroUnary, lineUnary, boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, stripZeroTransport, lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    endpointPkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed stripUnary zeroUnary sourceReadRoute
  have lineReadUnary : UnaryHistory lineRead :=
    unary_cont_closed sourceReadUnary lineUnary lineReadRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed lineUnary boundaryUnary boundaryReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row lineRead ∨ hsame row boundaryRead)
          (fun row : BHist => hsame row boundaryRead ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
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
      exact ⟨source.left, boundaryReadPkg⟩
  }
  exact
    ⟨cert, stripUnary, zeroUnary, lineUnary, boundaryUnary, sourceReadUnary, lineReadUnary,
      boundaryReadUnary, stripZeroTransport, sourceReadRoute, lineReadRoute,
      lineBoundaryRoute, boundaryReadRoute, endpointPkg, boundaryReadPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
