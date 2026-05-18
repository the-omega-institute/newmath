import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# MetricTriangleUniformEstimateUp finite carrier surface.
-/

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricTriangleUniformEstimateCarrier [AskSetup] [PackageSetup]
    (sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  UnaryHistory sourceMetric ∧ UnaryHistory targetMetric ∧ UnaryHistory graph ∧
    UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory center ∧
      UnaryHistory sourceBoundLeft ∧ UnaryHistory sourceBoundRight ∧
        UnaryHistory precision ∧ UnaryHistory targetBoundLeft ∧
          UnaryHistory targetBoundRight ∧ UnaryHistory targetTriangle ∧
            UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
              UnaryHistory localName ∧ Cont left center sourceBoundLeft ∧
                Cont right center sourceBoundRight ∧
                  Cont targetBoundLeft targetBoundRight targetTriangle ∧
                    Cont route provenance localName ∧ PkgSig bundle localName pkg ∧
                      hsame transport targetTriangle

theorem MetricTriangleUniformEstimateCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      PkgSig bundle localName pkg ->
        UnaryHistory sourceMetric ∧ UnaryHistory targetMetric ∧ UnaryHistory graph ∧
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory center ∧
            UnaryHistory sourceBoundLeft ∧ UnaryHistory sourceBoundRight ∧
              UnaryHistory precision ∧ UnaryHistory targetTriangle ∧
                Cont left center sourceBoundLeft ∧ Cont right center sourceBoundRight ∧
                  Cont targetBoundLeft targetBoundRight targetTriangle ∧
                    Cont route provenance localName ∧ PkgSig bundle localName pkg ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                        (fun row : BHist => hsame row localName)
                        (fun row : BHist => hsame row localName ∧ PkgSig bundle localName pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier pkgSig
  obtain ⟨unarySourceMetric, unaryTargetMetric, unaryGraph, unaryLeft, unaryRight,
    unaryCenter, unarySourceBoundLeft, unarySourceBoundRight, unaryPrecision,
    _unaryTargetBoundLeft, _unaryTargetBoundRight, unaryTargetTriangle, _unaryTransport,
    _unaryRoute, _unaryProvenance, unaryLocalName, sourceLeftRoute, sourceRightRoute,
    targetTriangleRoute, localNameRoute, _carrierPkgSig, _sameTransport⟩ := carrier
  have sourceLocal :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact And.intro (hsame_refl localName) unaryLocalName
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row localName ∧ UnaryHistory row)
        (fun row : BHist => hsame row localName)
        (fun row : BHist => hsame row localName ∧ PkgSig bundle localName pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName sourceLocal
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pkgSig
    }
  exact
    ⟨unarySourceMetric, unaryTargetMetric, unaryGraph, unaryLeft, unaryRight, unaryCenter,
      unarySourceBoundLeft, unarySourceBoundRight, unaryPrecision, unaryTargetTriangle,
      sourceLeftRoute, sourceRightRoute, targetTriangleRoute, localNameRoute, pkgSig, cert⟩

theorem MetricTriangleUniformEstimateCarrier_source_triangle_coherence [AskSetup] [PackageSetup]
    {sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName bundle pkg ->
      Cont sourceBoundLeft precision sourceBoundRight ->
        PkgSig bundle sourceBoundRight pkg ->
          SemanticNameCert
            (fun row : BHist =>
              MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
                sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
                targetTriangle transport route provenance localName bundle pkg ∧
                hsame row sourceBoundRight)
            (fun row : BHist => UnaryHistory row ∧ hsame row sourceBoundRight)
            (fun _row : BHist =>
              Cont left center sourceBoundLeft ∧ Cont sourceBoundLeft precision sourceBoundRight ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle sourceBoundRight pkg)
            hsame ∧ UnaryHistory sourceBoundLeft ∧ UnaryHistory sourceBoundRight := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceTriangle sourceBoundPkg
  have carrierWitness := carrier
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _graphUnary, _leftUnary, _rightUnary,
    _centerUnary, sourceBoundLeftUnary, sourceBoundRightUnary, _precisionUnary,
    _targetBoundLeftUnary, _targetBoundRightUnary, _targetTriangleUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, leftCenterSourceBound,
    _rightCenterSourceBound, _targetTriangleRoute, _routeProvenanceLocalName, localNamePkg,
    _transportTargetTriangle⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
            sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
            targetTriangle transport route provenance localName bundle pkg ∧
            hsame row sourceBoundRight)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sourceBoundRight
        (And.intro carrierWitness (hsame_refl sourceBoundRight))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          MetricTriangleUniformEstimateCarrier sourceMetric targetMetric graph left right center
            sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight
            targetTriangle transport route provenance localName bundle pkg ∧
            hsame row sourceBoundRight)
        (fun row : BHist => UnaryHistory row ∧ hsame row sourceBoundRight)
        (fun _row : BHist =>
          Cont left center sourceBoundLeft ∧ Cont sourceBoundLeft precision sourceBoundRight ∧
            PkgSig bundle localName pkg ∧ PkgSig bundle sourceBoundRight pkg)
        hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact
          And.intro
            (unary_transport sourceBoundRightUnary (hsame_symm sourceRow.right))
            sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨leftCenterSourceBound, sourceTriangle, localNamePkg, sourceBoundPkg⟩
    }
  exact And.intro semantic (And.intro sourceBoundLeftUnary sourceBoundRightUnary)

end BEDC.Derived.MetricTriangleUniformEstimateUp
