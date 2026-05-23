import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

def IsometricEmbeddingClassifier [AskSetup] [PackageSetup]
    (source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert source' target' graph' sourceDistance' targetDistance' reflection' transports'
      routes' provenance' localCert' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg
  IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
      transports routes provenance localCert bundle pkg ∧
    IsometricEmbeddingCarrier source' target' graph' sourceDistance' targetDistance' reflection'
      transports' routes' provenance' localCert' bundle pkg ∧
      hsame source source' ∧ hsame target target' ∧ hsame graph graph' ∧
        hsame sourceDistance sourceDistance' ∧ hsame targetDistance targetDistance' ∧
          hsame reflection reflection' ∧ hsame transports transports' ∧
            hsame routes routes' ∧ hsame provenance provenance' ∧ hsame localCert localCert'

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

theorem IsometricEmbeddingCarrier_completion_boundary [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont target transports completionConsumer ->
        PkgSig bundle completionConsumer pkg ->
          UnaryHistory completionConsumer ∧ Cont source graph target ∧
            Cont target transports completionConsumer ∧ PkgSig bundle reflection pkg ∧
              PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier targetTransportsConsumer consumerPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _sourceDistanceUnary, _targetDistanceUnary,
    _reflectionUnary, transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, _distanceReflection, pkgReflection, _localSemantic⟩ := carrier
  have consumerUnary : UnaryHistory completionConsumer :=
    unary_cont_closed targetUnary transportsUnary targetTransportsConsumer
  exact
    ⟨consumerUnary, sourceGraph, targetTransportsConsumer, pkgReflection, consumerPkg⟩

theorem IsometricEmbeddingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
          (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reflection pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
          UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧
            UnaryHistory reflection ∧ Cont source graph target ∧
              Cont sourceDistance targetDistance reflection ∧ PkgSig bundle reflection pkg := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame Cont ProbeBundle Pkg
  intro carrier
  obtain ⟨sourceUnary, targetUnary, graphUnary, sourceDistanceUnary, targetDistanceUnary,
    reflectionUnary, _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary,
    sourceGraphTarget, distanceReflection, reflectionPkg, localSemantic⟩ := carrier
  exact
    ⟨localSemantic, sourceUnary, targetUnary, graphUnary, sourceDistanceUnary,
      targetDistanceUnary, reflectionUnary, sourceGraphTarget, distanceReflection,
      reflectionPkg⟩

theorem IsometricEmbeddingCarrier_hausdorff_separation_boundary [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert hausdorffRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont target routes hausdorffRead ->
        Cont reflection hausdorffRead separatedRead ->
          PkgSig bundle separatedRead pkg ->
            UnaryHistory target ∧ UnaryHistory reflection ∧ UnaryHistory hausdorffRead ∧
              UnaryHistory separatedRead ∧ Cont source graph target ∧
                Cont sourceDistance targetDistance reflection ∧
                  Cont target routes hausdorffRead ∧
                    Cont reflection hausdorffRead separatedRead ∧
                      PkgSig bundle reflection pkg ∧ PkgSig bundle separatedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier targetRoutesHausdorff reflectionHausdorffSeparated separatedPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _sourceDistanceUnary, _targetDistanceUnary,
    reflectionUnary, _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, distanceReflection, pkgReflection, _localSemantic⟩ := carrier
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed targetUnary routesUnary targetRoutesHausdorff
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed reflectionUnary hausdorffUnary reflectionHausdorffSeparated
  exact
    ⟨targetUnary, reflectionUnary, hausdorffUnary, separatedUnary, sourceGraph,
      distanceReflection, targetRoutesHausdorff, reflectionHausdorffSeparated, pkgReflection,
      separatedPkg⟩

theorem IsometricEmbeddingCarrier_distance_preservation_obligation [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert reflectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont sourceDistance targetDistance reflection ->
        Cont reflection routes reflectedRead ->
          UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧ UnaryHistory reflection ∧
            UnaryHistory reflectedRead ∧ Cont sourceDistance targetDistance reflection ∧
              Cont reflection routes reflectedRead ∧ PkgSig bundle reflection pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier distanceReflection reflectionRoutesRead
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, sourceDistanceUnary, targetDistanceUnary,
    reflectionUnary, _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      _sourceGraph, _storedDistanceReflection, pkgReflection, _localSemantic⟩ := carrier
  have reflectedReadUnary : UnaryHistory reflectedRead :=
    unary_cont_closed reflectionUnary routesUnary reflectionRoutesRead
  exact
    ⟨sourceDistanceUnary, targetDistanceUnary, reflectionUnary, reflectedReadUnary,
      distanceReflection, reflectionRoutesRead, pkgReflection⟩

theorem IsometricEmbeddingCarrier_real_distance_route_determinacy [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont reflection routes consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
              (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reflection pkg)
              (fun row row' : BHist => hsame row row') ∧
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
              UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧
                UnaryHistory reflection ∧ UnaryHistory routes ∧ UnaryHistory consumer ∧
                  Cont source graph target ∧ Cont sourceDistance targetDistance reflection ∧
                    Cont reflection routes consumer ∧ PkgSig bundle reflection pkg ∧
                      PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier reflectionRoutesConsumer consumerPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, sourceDistanceUnary, targetDistanceUnary,
    reflectionUnary, _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, distanceReflection, pkgReflection, localSemantic⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed reflectionUnary routesUnary reflectionRoutesConsumer
  exact
    ⟨localSemantic, sourceUnary, targetUnary, graphUnary, sourceDistanceUnary,
      targetDistanceUnary, reflectionUnary, routesUnary, consumerUnary, sourceGraph,
      distanceReflection, reflectionRoutesConsumer, pkgReflection, consumerPkg⟩

theorem IsometricEmbeddingCarrier_completion_reflection_handoff [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert completionConsumer separatedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont target transports completionConsumer ->
        Cont reflection routes separatedConsumer ->
          PkgSig bundle completionConsumer pkg ->
            PkgSig bundle separatedConsumer pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
                    (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reflection pkg)
                    hsame ∧
                UnaryHistory target ∧ UnaryHistory reflection ∧
                  UnaryHistory completionConsumer ∧ UnaryHistory separatedConsumer ∧
                    Cont source graph target ∧ Cont sourceDistance targetDistance reflection ∧
                      Cont target transports completionConsumer ∧
                        Cont reflection routes separatedConsumer ∧
                          PkgSig bundle reflection pkg ∧
                            PkgSig bundle completionConsumer pkg ∧
                              PkgSig bundle separatedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier targetTransportsCompletion reflectionRoutesSeparated completionPkg separatedPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _sourceDistanceUnary, _targetDistanceUnary,
    reflectionUnary, transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, distanceReflection, reflectionPkg, localSemantic⟩ := carrier
  have completionUnary : UnaryHistory completionConsumer :=
    unary_cont_closed targetUnary transportsUnary targetTransportsCompletion
  have separatedUnary : UnaryHistory separatedConsumer :=
    unary_cont_closed reflectionUnary routesUnary reflectionRoutesSeparated
  exact
    ⟨localSemantic, targetUnary, reflectionUnary, completionUnary, separatedUnary, sourceGraph,
      distanceReflection, targetTransportsCompletion, reflectionRoutesSeparated, reflectionPkg,
      completionPkg, separatedPkg⟩

theorem IsometricEmbeddingCarrier_distance_route_reflection_lock [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert completionConsumer separatedConsumer hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont target transports completionConsumer ->
        Cont reflection routes separatedConsumer ->
          PkgSig bundle completionConsumer pkg ->
            PkgSig bundle separatedConsumer pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
                    (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reflection pkg)
                    hsame ∧
                UnaryHistory completionConsumer ∧ UnaryHistory separatedConsumer ∧
                  Cont source graph target ∧ Cont sourceDistance targetDistance reflection ∧
                    Cont target transports completionConsumer ∧
                      Cont reflection routes separatedConsumer ∧
                        PkgSig bundle reflection pkg ∧ PkgSig bundle completionConsumer pkg ∧
                          PkgSig bundle separatedConsumer pkg ∧
                            (Cont separatedConsumer (BHist.e0 hostTail) reflection -> False) ∧
                              (Cont separatedConsumer (BHist.e1 hostTail) reflection -> False) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier targetTransportsCompletion reflectionRoutesSeparated completionPkg separatedPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _sourceDistanceUnary, _targetDistanceUnary,
    reflectionUnary, transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraph, distanceReflection, reflectionPkg, localSemantic⟩ := carrier
  have completionUnary : UnaryHistory completionConsumer :=
    unary_cont_closed targetUnary transportsUnary targetTransportsCompletion
  have separatedUnary : UnaryHistory separatedConsumer :=
    unary_cont_closed reflectionUnary routesUnary reflectionRoutesSeparated
  have e0Refusal : Cont separatedConsumer (BHist.e0 hostTail) reflection -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.left reflectionRoutesSeparated back
  have e1Refusal : Cont separatedConsumer (BHist.e1 hostTail) reflection -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.right reflectionRoutesSeparated back
  exact
    ⟨localSemantic, completionUnary, separatedUnary, sourceGraph, distanceReflection,
      targetTransportsCompletion, reflectionRoutesSeparated, reflectionPkg, completionPkg,
      separatedPkg, e0Refusal, e1Refusal⟩

theorem IsometricEmbeddingCarrier_sibling_completion_lattice [AskSetup] [PackageSetup]
    {source target graph sourceDistance targetDistance reflection transports routes provenance
      localCert realConsumer completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricEmbeddingCarrier source target graph sourceDistance targetDistance reflection
        transports routes provenance localCert bundle pkg ->
      Cont reflection routes realConsumer ->
        Cont target transports completionConsumer ->
          PkgSig bundle realConsumer pkg ->
            PkgSig bundle completionConsumer pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧
                  UnaryHistory reflection ∧ UnaryHistory realConsumer ∧
                    UnaryHistory completionConsumer ∧ Cont source graph target ∧
                      Cont sourceDistance targetDistance reflection ∧
                        Cont reflection routes realConsumer ∧
                          Cont target transports completionConsumer ∧
                            PkgSig bundle reflection pkg ∧ PkgSig bundle realConsumer pkg ∧
                              PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier reflectionRoutesReal targetTransportsCompletion realPkg completionPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, sourceDistanceUnary, targetDistanceUnary,
    reflectionUnary, transportsUnary, routesUnary, _provenanceUnary, _localCertUnary,
      sourceGraphTarget, distanceReflection, reflectionPkg, _localSemantic⟩ := carrier
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed reflectionUnary routesUnary reflectionRoutesReal
  have completionConsumerUnary : UnaryHistory completionConsumer :=
    unary_cont_closed targetUnary transportsUnary targetTransportsCompletion
  exact
    ⟨sourceUnary, targetUnary, graphUnary, sourceDistanceUnary, targetDistanceUnary,
      reflectionUnary, realConsumerUnary, completionConsumerUnary, sourceGraphTarget,
      distanceReflection, reflectionRoutesReal, targetTransportsCompletion, reflectionPkg,
      realPkg, completionPkg⟩

end BEDC.Derived.IsometricEmbeddingUp
