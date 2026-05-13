import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IsometricEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IsometricEmbeddingCarrier [AskSetup] [PackageSetup]
    (source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
    UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧ UnaryHistory reflection ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont source graph target ∧
          Cont sourceDistance targetDistance reflection ∧ PkgSig bundle reflection pkg ∧
            SemanticNameCert
              (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
              (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reflection pkg)
              (fun row row' : BHist => hsame row row')

theorem IsometricEmbeddingCarrier_classifier_transport [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert source' graph' target' sourceDistance' targetDistance' reflection' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      hsame source source' ->
        hsame graph graph' ->
          hsame sourceDistance sourceDistance' ->
            hsame targetDistance targetDistance' ->
              Cont source' graph' target' ->
                Cont sourceDistance' targetDistance' reflection' ->
                  hsame target target' ∧ hsame reflection reflection' ∧
                    Cont source graph target ∧ Cont sourceDistance targetDistance reflection ∧
                      PkgSig bundle reflection pkg := by
  intro carrier sameSource sameGraph sameSourceDistance sameTargetDistance
  intro transportedGraph transportedReflection
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _sourceDistanceUnary, _targetDistanceUnary,
    _reflectionUnary, _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, distanceReflection, pkgReflection, _localSemantic⟩ := carrier
  have sameTarget : hsame target target' :=
    cont_respects_hsame sameSource sameGraph sourceGraph transportedGraph
  have sameReflection : hsame reflection reflection' :=
    cont_respects_hsame sameSourceDistance sameTargetDistance distanceReflection
      transportedReflection
  exact ⟨sameTarget, sameReflection, sourceGraph, distanceReflection, pkgReflection⟩

theorem IsometricEmbeddingCarrier_separated_consumer_route [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont reflection routes consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory reflection ∧ UnaryHistory consumer ∧ Cont source graph target ∧
              Cont sourceDistance targetDistance reflection ∧ Cont reflection routes consumer ∧
                PkgSig bundle reflection pkg ∧ PkgSig bundle consumer pkg := by
  intro carrier reflectionRoutesConsumer consumerPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _sourceDistanceUnary, _targetDistanceUnary,
    reflectionUnary, _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, distanceReflection, pkgReflection, _localSemantic⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed reflectionUnary routesUnary reflectionRoutesConsumer
  exact
    ⟨sourceUnary, targetUnary, graphUnary, reflectionUnary, consumerUnary, sourceGraph,
      distanceReflection, reflectionRoutesConsumer, pkgReflection, consumerPkg⟩

end BEDC.Derived.IsometricEmbeddingUp
