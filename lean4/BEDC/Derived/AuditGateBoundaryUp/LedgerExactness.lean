import BEDC.Derived.AuditGateBoundaryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditGateBoundaryCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont sourceScan dependencyReport markerResolution ->
        Cont markerResolution originLedger transport ->
          Cont transport route provenance ->
            Cont provenance gap nameCert ->
              Cont nameCert route verdict ->
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row sourceScan ∨ hsame row dependencyReport ∨
                      hsame row markerResolution ∨ hsame row originLedger)
                  (fun row : BHist => UnaryHistory row ∧ hsame row gap)
                  (fun row : BHist =>
                    hsame row verdict ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle nameCert pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier sourceDependency markerOrigin transportRoute provenanceGap verdictRoute
  obtain ⟨sourceUnary, dependencyUnary, markerUnary, originUnary, _transportUnary, routeUnary,
    _provenanceUnary, _gapUnary, _nameUnary, dependencyGap, nameGap, _sourceDependencyMarker,
    _markerOriginTransport, _transportRouteProvenance, _provenanceGapName, provenancePkg,
    namePkg⟩ := carrier
  have provenanceGapToGap : Cont provenance gap gap :=
    cont_result_hsame_transport provenanceGap nameGap
  have provenanceEmpty : hsame provenance BHist.Empty :=
    cont_left_unit_unique provenanceGapToGap
  have transportRouteEmpty :=
    cont_empty_result_inversion
      (cont_result_hsame_transport transportRoute provenanceEmpty)
  have transportEmpty : hsame transport BHist.Empty := transportRouteEmpty.left
  have routeEmpty : hsame route BHist.Empty := transportRouteEmpty.right
  have markerOriginEmpty :=
    cont_empty_result_inversion
      (cont_result_hsame_transport markerOrigin transportEmpty)
  have markerEmpty : hsame markerResolution BHist.Empty := markerOriginEmpty.left
  have originEmpty : hsame originLedger BHist.Empty := markerOriginEmpty.right
  have sourceEmpty : hsame sourceScan BHist.Empty ∧ hsame dependencyReport BHist.Empty :=
    cont_empty_result_inversion
      (cont_result_hsame_transport sourceDependency markerEmpty)
  have gapEmpty : hsame gap BHist.Empty :=
    hsame_trans (hsame_symm dependencyGap) sourceEmpty.right
  have nameEmpty : hsame nameCert BHist.Empty :=
    hsame_trans nameGap gapEmpty
  have verdictEmpty : hsame verdict BHist.Empty :=
    have verdictName : hsame verdict nameCert := by
      cases routeEmpty
      exact cont_deterministic verdictRoute (cont_right_unit nameCert)
    hsame_trans verdictName nameEmpty
  have sourceSameGap : hsame sourceScan gap :=
    hsame_trans sourceEmpty.left (hsame_symm gapEmpty)
  have dependencySameGap : hsame dependencyReport gap :=
    hsame_trans sourceEmpty.right (hsame_symm gapEmpty)
  have markerSameGap : hsame markerResolution gap :=
    hsame_trans markerEmpty (hsame_symm gapEmpty)
  have originSameGap : hsame originLedger gap :=
    hsame_trans originEmpty (hsame_symm gapEmpty)
  have verdictSameGap : hsame verdict gap :=
    hsame_trans verdictEmpty (hsame_symm gapEmpty)
  have sourceAtSource :
      (fun row : BHist =>
        hsame row sourceScan ∨ hsame row dependencyReport ∨ hsame row markerResolution ∨
          hsame row originLedger) sourceScan := by
    exact Or.inl (hsame_refl sourceScan)
  exact {
    core := {
      carrier_inhabited := Exists.intro sourceScan sourceAtSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        cases source with
        | inl sameSource =>
            exact Or.inl (hsame_trans (hsame_symm same) sameSource)
        | inr rest =>
            cases rest with
            | inl sameDependency =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameDependency))
            | inr rest =>
                cases rest with
                | inl sameMarker =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameMarker)))
                | inr sameOrigin =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm same) sameOrigin)))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameSource =>
          exact ⟨unary_transport sourceUnary (hsame_symm sameSource),
            hsame_trans sameSource sourceSameGap⟩
      | inr rest =>
          cases rest with
          | inl sameDependency =>
              exact ⟨unary_transport dependencyUnary (hsame_symm sameDependency),
                hsame_trans sameDependency dependencySameGap⟩
          | inr rest =>
              cases rest with
              | inl sameMarker =>
                  exact ⟨unary_transport markerUnary (hsame_symm sameMarker),
                    hsame_trans sameMarker markerSameGap⟩
              | inr sameOrigin =>
                  exact ⟨unary_transport originUnary (hsame_symm sameOrigin),
                    hsame_trans sameOrigin originSameGap⟩
    ledger_sound := by
      intro row source
      have rowGap : hsame row gap := by
        cases source with
        | inl sameSource =>
            exact hsame_trans sameSource sourceSameGap
        | inr rest =>
            cases rest with
            | inl sameDependency =>
                exact hsame_trans sameDependency dependencySameGap
            | inr rest =>
                cases rest with
                | inl sameMarker =>
                    exact hsame_trans sameMarker markerSameGap
                | inr sameOrigin =>
                    exact hsame_trans sameOrigin originSameGap
      exact ⟨hsame_trans rowGap (hsame_symm verdictSameGap), provenancePkg, namePkg⟩
  }

end BEDC.Derived.AuditGateBoundaryUp
