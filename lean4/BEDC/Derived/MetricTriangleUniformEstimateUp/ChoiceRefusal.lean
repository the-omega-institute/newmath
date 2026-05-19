import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_choice_refusal
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName finiteRoute refusedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
    Cont precision targetTriangle finiteRoute ->
    hsame refusedRoute finiteRoute ->
    PkgSig bundle finiteRoute pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row finiteRoute ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row center ∨ hsame row precision ∨ hsame row targetTriangle ∨
            hsame row finiteRoute)
        (fun row : BHist => hsame row finiteRoute ∧ PkgSig bundle finiteRoute pkg)
        hsame ∧ UnaryHistory refusedRoute ∧ hsame refusedRoute finiteRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier precisionTargetFinite sameRefusedFinite finitePkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, _sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    _localNamePkg, _transportTargetTriangle⟩ := carrier
  have finiteUnary : UnaryHistory finiteRoute :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTargetFinite
  have refusedUnary : UnaryHistory refusedRoute :=
    unary_transport finiteUnary (hsame_symm sameRefusedFinite)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row finiteRoute ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row center ∨ hsame row precision ∨ hsame row targetTriangle ∨
            hsame row finiteRoute)
        (fun row : BHist => hsame row finiteRoute ∧ PkgSig bundle finiteRoute pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro finiteRoute
        ⟨hsame_refl finiteRoute, finiteUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, finitePkg⟩
  }
  exact ⟨cert, refusedUnary, sameRefusedFinite⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
