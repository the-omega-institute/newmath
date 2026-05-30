import BEDC.Derived.BoundedVariationUp

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedVariationPartitionLedger_refinement_ledger_scope [AskSetup] [PackageSetup]
    {interval partition edge endpoint dyadic variation refinement transport route provenance
      nameCert variationScope scopeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationPartitionLedger interval partition edge endpoint dyadic variation refinement
        transport route provenance nameCert bundle pkg ->
      Cont edge refinement variationScope ->
        Cont variationScope transport scopeRoute ->
          PkgSig bundle scopeRoute pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row variation ∨ hsame row variationScope ∨ hsame row scopeRoute)
                (fun row : BHist =>
                  hsame row refinement ∨ Cont edge refinement variationScope ∨
                    Cont variationScope transport scopeRoute)
                (fun row : BHist =>
                  PkgSig bundle scopeRoute pkg ∧
                    (hsame row variationScope ∨ hsame row scopeRoute))
                hsame ∧
              hsame variation variationScope ∧ UnaryHistory variationScope ∧
                UnaryHistory scopeRoute ∧ Cont edge refinement variationScope ∧
                  Cont variationScope transport scopeRoute ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle scopeRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro ledger edgeRefinementScope scopeTransportRoute scopePkg
  obtain ⟨_intervalUnary, _partitionUnary, edgeUnary, _endpointUnary, _dyadicUnary,
    _variationUnary, refinementUnary, transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _intervalPartitionEndpoint, _endpointDyadicEdge,
    edgeRefinementVariation, _variationTransportRoute, _routeProvenanceNameCert,
    _variationSameAppend, provenancePkg⟩ := ledger
  have sameVariationScope : hsame variation variationScope :=
    cont_respects_hsame (hsame_refl edge) (hsame_refl refinement) edgeRefinementVariation
      edgeRefinementScope
  have variationScopeUnary : UnaryHistory variationScope :=
    unary_cont_closed edgeUnary refinementUnary edgeRefinementScope
  have scopeRouteUnary : UnaryHistory scopeRoute :=
    unary_cont_closed variationScopeUnary transportUnary scopeTransportRoute
  have sourceScope :
      (fun row : BHist =>
        hsame row variation ∨ hsame row variationScope ∨ hsame row scopeRoute)
        variationScope := by
    exact Or.inr (Or.inl (hsame_refl variationScope))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row variation ∨ hsame row variationScope ∨ hsame row scopeRoute)
          (fun row : BHist =>
            hsame row refinement ∨ Cont edge refinement variationScope ∨
              Cont variationScope transport scopeRoute)
          (fun row : BHist =>
            PkgSig bundle scopeRoute pkg ∧
              (hsame row variationScope ∨ hsame row scopeRoute))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro variationScope sourceScope
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
        cases source with
        | inl rowVariation =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowVariation)
        | inr rest =>
            cases rest with
            | inl rowVariationScope =>
                exact Or.inr
                  (Or.inl (hsame_trans (hsame_symm sameRows) rowVariationScope))
            | inr rowScopeRoute =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowScopeRoute))
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inl edgeRefinementScope)
    ledger_sound := by
      intro _row source
      cases source with
      | inl rowVariation =>
          exact ⟨scopePkg, Or.inl (hsame_trans rowVariation sameVariationScope)⟩
      | inr rest =>
          cases rest with
          | inl rowVariationScope =>
              exact ⟨scopePkg, Or.inl rowVariationScope⟩
          | inr rowScopeRoute =>
              exact ⟨scopePkg, Or.inr rowScopeRoute⟩
  }
  exact
    ⟨cert, sameVariationScope, variationScopeUnary, scopeRouteUnary,
      edgeRefinementScope, scopeTransportRoute, provenancePkg, scopePkg⟩

end BEDC.Derived.BoundedVariationUp
