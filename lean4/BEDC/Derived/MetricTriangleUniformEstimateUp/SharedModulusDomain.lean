import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_shared_modulus_domain [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName sourceReadLeft sourceReadRight targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont sourceBoundLeft precision sourceReadLeft ->
        Cont sourceBoundRight precision sourceReadRight ->
          Cont targetTriangle localName targetRead ->
            PkgSig bundle targetRead pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row precision ∨ hsame row sourceReadLeft ∨
                    hsame row sourceReadRight ∨ hsame row targetTriangle ∨
                      hsame row targetRead)
                (fun row : BHist => PkgSig bundle targetRead pkg ∧ hsame row targetRead)
                hsame ∧ UnaryHistory sourceReadLeft ∧ UnaryHistory sourceReadRight ∧
                  UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier leftPrecisionRead rightPrecisionRead targetTriangleRead targetReadPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    _localNamePkg, _transportTargetTriangle⟩ := carrier
  have sourceReadLeftUnary : UnaryHistory sourceReadLeft :=
    unary_cont_closed sourceBoundLeftUnary precisionUnary leftPrecisionRead
  have sourceReadRightUnary : UnaryHistory sourceReadRight :=
    unary_cont_closed sourceBoundRightUnary precisionUnary rightPrecisionRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetTriangleUnary localNameUnary targetTriangleRead
  have sourceTarget :
      (fun row : BHist => hsame row targetRead ∧ UnaryHistory row) targetRead := by
    exact ⟨hsame_refl targetRead, targetReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row precision ∨ hsame row sourceReadLeft ∨ hsame row sourceReadRight ∨
            hsame row targetTriangle ∨ hsame row targetRead)
        (fun row : BHist => PkgSig bundle targetRead pkg ∧ hsame row targetRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro targetRead sourceTarget
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
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨targetReadPkg, sourceRow.left⟩
    }
  exact ⟨cert, sourceReadLeftUnary, sourceReadRightUnary, targetReadUnary⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
