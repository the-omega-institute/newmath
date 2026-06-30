import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_scope_binding [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint sourceRead scopedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont strip zero sourceRead ->
        Cont sourceRead line scopedRead ->
          PkgSig bundle scopedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strip ∨ hsame row zero ∨ hsame row line ∨ hsame row boundary ∨
                    hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont strip zero sourceRead ∧
                    Cont sourceRead line scopedRead ∧ PkgSig bundle scopedRead pkg ∧
                      PkgSig bundle endpoint pkg)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory scopedRead ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute scopedRoute scopedPkg
  obtain ⟨stripUnary, zeroUnary, lineUnary, _boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, _stripZeroTransport, _lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    endpointPkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed stripUnary zeroUnary sourceRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed sourceReadUnary lineUnary scopedRoute
  have sourceAtScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead :=
    ⟨hsame_refl scopedRead, scopedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strip ∨ hsame row zero ∨ hsame row line ∨ hsame row boundary ∨
              hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strip zero sourceRead ∧ Cont sourceRead line scopedRead ∧
              PkgSig bundle scopedRead pkg ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceAtScoped
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, scopedRoute, scopedPkg, endpointPkg⟩
  }
  exact ⟨cert, sourceReadUnary, scopedReadUnary, endpointPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
