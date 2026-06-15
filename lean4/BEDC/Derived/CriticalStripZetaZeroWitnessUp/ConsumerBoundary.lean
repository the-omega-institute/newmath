import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessPacket_consumer_boundary [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name endpoint consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessPacket strip zero line boundary transport route provenance name
        endpoint bundle pkg ->
      Cont endpoint name consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row zero ∨ hsame row line ∨ hsame row boundary ∨
                  hsame row endpoint ∨ hsame row consumerRead)
              (fun row : BHist =>
                hsame row consumerRead ∧ Cont endpoint name consumerRead ∧
                  PkgSig bundle consumerRead pkg)
              hsame ∧
            UnaryHistory zero ∧ UnaryHistory line ∧ UnaryHistory boundary ∧
              UnaryHistory endpoint ∧ UnaryHistory name ∧ UnaryHistory consumerRead ∧
                Cont endpoint name consumerRead ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet consumerRoute consumerPkg
  obtain ⟨_stripUnary, zeroUnary, lineUnary, boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameUnary, endpointUnary, _stripZeroTransport, _lineBoundaryRoute,
    _transportRouteEndpoint, _endpointProvenanceName, _endpointSameTransportRoute,
    endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary nameUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zero ∨ hsame row line ∨ hsame row boundary ∨
              hsame row endpoint ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont endpoint name consumerRead ∧
              PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact ⟨source.left, consumerRoute, consumerPkg⟩
  }
  exact
    ⟨cert, zeroUnary, lineUnary, boundaryUnary, endpointUnary, nameUnary, consumerUnary,
      consumerRoute, endpointPkg, consumerPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
