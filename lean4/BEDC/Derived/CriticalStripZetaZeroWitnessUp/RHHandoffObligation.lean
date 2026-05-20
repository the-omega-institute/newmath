import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_rh_handoff_obligation [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint premiseRead lineRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont strip zero premiseRead ->
        Cont line boundary lineRead ->
          Cont premiseRead lineRead handoffRead ->
            PkgSig bundle handoffRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row premiseRead ∨ hsame row lineRead ∨ hsame row handoffRead)
                  (fun row : BHist => hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
                  hsame ∧
                UnaryHistory premiseRead ∧ UnaryHistory lineRead ∧ UnaryHistory handoffRead ∧
                  Cont strip zero premiseRead ∧ Cont line boundary lineRead ∧
                    Cont premiseRead lineRead handoffRead ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet premiseRoute lineRoute handoffRoute handoffPkg
  obtain ⟨stripUnary, zeroUnary, lineUnary, boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _endpointUnary, _stripZeroTransport,
    _lineBoundaryRoute, _transportRouteEndpoint, _endpointProvenanceName,
    _endpointSameTransportRoute, endpointPkg⟩ := packet
  have premiseUnary : UnaryHistory premiseRead :=
    unary_cont_closed stripUnary zeroUnary premiseRoute
  have lineReadUnary : UnaryHistory lineRead :=
    unary_cont_closed lineUnary boundaryUnary lineRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed premiseUnary lineReadUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premiseRead ∨ hsame row lineRead ∨ hsame row handoffRead)
          (fun row : BHist => hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact ⟨source.left, handoffPkg⟩
  }
  exact
    ⟨cert, premiseUnary, lineReadUnary, handoffUnary, premiseRoute, lineRoute,
      handoffRoute, endpointPkg, handoffPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
