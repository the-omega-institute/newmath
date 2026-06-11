import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_uniformmodulus_boundary_exactness
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName targetRead boundaryRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg →
      Cont sourceBoundLeft precision sourceBoundRight →
        Cont precision targetTriangle targetRead →
          Cont targetRead localName boundaryRead →
            Cont boundaryRead localName consumer →
              PkgSig bundle boundaryRead pkg →
                PkgSig bundle consumer pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row precision ∨ hsame row sourceBoundLeft ∨
                        hsame row sourceBoundRight ∨ hsame row targetTriangle ∨
                          hsame row boundaryRead)
                    (fun row : BHist =>
                      PkgSig bundle boundaryRead pkg ∧ hsame row boundaryRead)
                    hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier _sourceBoundaryRoute precisionTargetRead targetLocalBoundary
    boundaryLocalConsumer boundaryPkg _consumerPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, sourceBoundLeftUnary, _sourceBoundRightUnary, precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    _localNamePkg, _transportTargetTriangle⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetTriangleUnary precisionTargetRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed targetReadUnary localNameUnary targetLocalBoundary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed boundaryReadUnary localNameUnary boundaryLocalConsumer
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row precision ∨ hsame row sourceBoundLeft ∨ hsame row sourceBoundRight ∨
            hsame row targetTriangle ∨ hsame row boundaryRead)
        (fun row : BHist => PkgSig bundle boundaryRead pkg ∧ hsame row boundaryRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro boundaryRead sourceBoundary
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨boundaryPkg, source.left⟩
    }
  exact ⟨cert, boundaryReadUnary, consumerUnary⟩

theorem MetricTriangleUniformEstimateUniformModulusBoundaryExactness
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName boundaryRead modulusRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg →
    Cont sourceBoundLeft sourceBoundRight boundaryRead →
    Cont boundaryRead targetTriangle modulusRead →
    Cont modulusRead localName exactRead →
    PkgSig bundle exactRead pkg →
      SemanticNameCert
        (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row center ∨ hsame row sourceBoundLeft ∨ hsame row sourceBoundRight ∨
            hsame row targetBoundLeft ∨ hsame row targetBoundRight ∨
              hsame row targetTriangle ∨ hsame row boundaryRead ∨
                hsame row modulusRead ∨ hsame row exactRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont sourceBoundLeft sourceBoundRight boundaryRead ∧
            Cont boundaryRead targetTriangle modulusRead ∧
              Cont modulusRead localName exactRead ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle exactRead pkg)
        hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory modulusRead ∧
          UnaryHistory exactRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier boundaryRoute modulusRoute exactRoute exactPkg
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, _precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName,
    localNamePkg, _transportTargetTriangle⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sourceBoundLeftUnary sourceBoundRightUnary boundaryRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundaryReadUnary targetTriangleUnary modulusRoute
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed modulusReadUnary localNameUnary exactRoute
  have sourceExact :
      (fun row : BHist => hsame row exactRead ∧ UnaryHistory row) exactRead := by
    exact ⟨hsame_refl exactRead, exactReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row center ∨ hsame row sourceBoundLeft ∨ hsame row sourceBoundRight ∨
            hsame row targetBoundLeft ∨ hsame row targetBoundRight ∨
              hsame row targetTriangle ∨ hsame row boundaryRead ∨
                hsame row modulusRead ∨ hsame row exactRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont sourceBoundLeft sourceBoundRight boundaryRead ∧
            Cont boundaryRead targetTriangle modulusRead ∧
              Cont modulusRead localName exactRead ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle exactRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exactRead sourceExact
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, boundaryRoute, modulusRoute, exactRoute, localNamePkg, exactPkg⟩
    }
  exact ⟨cert, boundaryReadUnary, modulusReadUnary, exactReadUnary⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
