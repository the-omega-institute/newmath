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

theorem AuditGateBoundaryUp_StdBridge [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont nameCert bridge gap ->
        SemanticNameCert
          (fun row : BHist =>
            hsame row sourceScan ∨ hsame row dependencyReport ∨ hsame row markerResolution ∨
              hsame row originLedger ∨ hsame row bridge)
          (fun row : BHist => hsame row bridge ∧ Cont nameCert bridge gap)
          (fun row : BHist =>
            hsame row gap ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier bridgeRoute
  obtain ⟨sourceUnary, dependencyUnary, markerUnary, originUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _gapUnary, _nameUnary, dependencyGap, nameGap, sourceDependencyMarker,
    markerOriginTransport, _transportRouteProvenance, provenanceGapName, provenancePkg,
    namePkg⟩ := carrier
  have provenanceGapToGap : Cont provenance gap gap :=
    cont_result_hsame_transport provenanceGapName nameGap
  have provenanceEmpty : hsame provenance BHist.Empty :=
    cont_left_unit_unique provenanceGapToGap
  have transportRouteEmpty :=
    cont_empty_result_inversion
      (cont_result_hsame_transport _transportRouteProvenance provenanceEmpty)
  have transportEmpty : hsame transport BHist.Empty := transportRouteEmpty.left
  have routeEmpty : hsame route BHist.Empty := transportRouteEmpty.right
  have markerOriginEmpty :=
    cont_empty_result_inversion
      (cont_result_hsame_transport markerOriginTransport transportEmpty)
  have markerEmpty : hsame markerResolution BHist.Empty := markerOriginEmpty.left
  have originEmpty : hsame originLedger BHist.Empty := markerOriginEmpty.right
  have sourceDependencyEmpty : hsame sourceScan BHist.Empty ∧ hsame dependencyReport BHist.Empty :=
    cont_empty_result_inversion
      (cont_result_hsame_transport sourceDependencyMarker markerEmpty)
  have gapEmpty : hsame gap BHist.Empty :=
    hsame_trans (hsame_symm dependencyGap) sourceDependencyEmpty.right
  have nameEmpty : hsame nameCert BHist.Empty :=
    hsame_trans nameGap gapEmpty
  have bridgeEmpty : hsame bridge BHist.Empty :=
    (cont_empty_result_inversion
      (cont_result_hsame_transport bridgeRoute gapEmpty)).right
  have sourceSameBridge : hsame sourceScan bridge :=
    hsame_trans sourceDependencyEmpty.left (hsame_symm bridgeEmpty)
  have dependencyBridge : hsame dependencyReport bridge :=
    hsame_trans sourceDependencyEmpty.right (hsame_symm bridgeEmpty)
  have markerSameBridge : hsame markerResolution bridge :=
    hsame_trans markerEmpty (hsame_symm bridgeEmpty)
  have originBridge : hsame originLedger bridge :=
    hsame_trans originEmpty (hsame_symm bridgeEmpty)
  have gapSameBridge : hsame gap bridge :=
    hsame_trans gapEmpty (hsame_symm bridgeEmpty)
  have sourceAtBridge :
      (fun row : BHist =>
        hsame row sourceScan ∨ hsame row dependencyReport ∨ hsame row markerResolution ∨
          hsame row originLedger ∨ hsame row bridge) bridge := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl bridge))))
  exact {
    core := {
      carrier_inhabited := Exists.intro bridge sourceAtBridge
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
                | inr rest =>
                    cases rest with
                    | inl sameOrigin =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameOrigin))))
                    | inr sameBridge =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm same) sameBridge))))
    }
    pattern_sound := by
      intro row source
      have rowBridge : hsame row bridge := by
        cases source with
        | inl sameSource =>
            exact hsame_trans sameSource sourceSameBridge
        | inr rest =>
            cases rest with
            | inl sameDependency =>
                exact hsame_trans sameDependency dependencyBridge
            | inr rest =>
                cases rest with
                | inl sameMarker =>
                    exact hsame_trans sameMarker markerSameBridge
                | inr rest =>
                    cases rest with
                    | inl sameOrigin =>
                        exact hsame_trans sameOrigin originBridge
                    | inr sameBridge =>
                        exact sameBridge
      exact And.intro rowBridge bridgeRoute
    ledger_sound := by
      intro row source
      have rowBridge : hsame row bridge := by
        cases source with
        | inl sameSource =>
            exact hsame_trans sameSource sourceSameBridge
        | inr rest =>
            cases rest with
            | inl sameDependency =>
                exact hsame_trans sameDependency dependencyBridge
            | inr rest =>
                cases rest with
                | inl sameMarker =>
                    exact hsame_trans sameMarker markerSameBridge
                | inr rest =>
                    cases rest with
                    | inl sameOrigin =>
                        exact hsame_trans sameOrigin originBridge
                    | inr sameBridge =>
                        exact sameBridge
      exact ⟨hsame_trans rowBridge (hsame_symm gapSameBridge), provenancePkg, namePkg⟩
  }

end BEDC.Derived.AuditGateBoundaryUp
