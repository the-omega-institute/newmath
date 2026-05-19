import BEDC.Derived.MetricTriangleUniformEstimateUp

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricTriangleUniformEstimateCarrier_root_unblock_certificate_spine
    [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName handoff consumer spine : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg ->
      Cont sourceBoundLeft precision sourceBoundRight ->
      Cont targetTriangle localName handoff ->
      Cont handoff sourceBoundRight consumer ->
      Cont consumer provenance spine ->
      PkgSig bundle spine pkg ->
        SemanticNameCert
          (fun row : BHist =>
            MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
              sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
              targetTriangle transport route provenance localName bundle pkg ∧ hsame row spine)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row sourceBoundRight ∨ hsame row targetTriangle ∨ hsame row handoff ∨
                hsame row consumer ∨ hsame row spine))
          (fun _row : BHist =>
            Cont sourceBoundLeft precision sourceBoundRight ∧
              Cont targetTriangle localName handoff ∧ Cont handoff sourceBoundRight consumer ∧
                Cont consumer provenance spine ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle spine pkg)
          hsame ∧ UnaryHistory spine := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier sourceTriangle targetTriangleHandoff handoffSourceConsumer
    consumerProvenanceSpine spinePkg
  have carrierWitness :
      MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
        sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
        targetTriangle transport route provenance localName bundle pkg := carrier
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, _sourceBoundLeftUnary, sourceBoundRightUnary, _precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, targetTriangleUnary, _transportUnary,
    _routeUnary, provenanceUnary, _localNameUnary, _leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName, localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed targetTriangleUnary _localNameUnary targetTriangleHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary sourceBoundRightUnary handoffSourceConsumer
  have spineUnary : UnaryHistory spine :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceSpine
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
            sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
            targetTriangle transport route provenance localName bundle pkg ∧ hsame row spine)
        (fun row : BHist =>
          UnaryHistory row ∧
            (hsame row sourceBoundRight ∨ hsame row targetTriangle ∨ hsame row handoff ∨
              hsame row consumer ∨ hsame row spine))
        (fun _row : BHist =>
          Cont sourceBoundLeft precision sourceBoundRight ∧
            Cont targetTriangle localName handoff ∧ Cont handoff sourceBoundRight consumer ∧
              Cont consumer provenance spine ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle spine pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro spine
          ⟨carrierWitness, hsame_refl spine⟩
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
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨unary_transport spineUnary (hsame_symm sourceRow.right),
            Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceTriangle, targetTriangleHandoff, handoffSourceConsumer,
            consumerProvenanceSpine, localNamePkg, spinePkg⟩
    }
  exact ⟨cert, spineUnary⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
