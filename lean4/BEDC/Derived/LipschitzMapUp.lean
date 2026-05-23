import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LipschitzMapCarrier [AskSetup] [PackageSetup]
    (source target bound graph modulus transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory bound ∧ UnaryHistory graph ∧
    UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory localCert ∧
      Cont graph bound modulus ∧ Cont modulus routes provenance ∧
        PkgSig bundle provenance pkg

def LipschitzMapClassifier [AskSetup] [PackageSetup]
    (source target bound graph modulus transports routes provenance localCert source' target'
      bound' graph' modulus' transports' routes' provenance' localCert' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
      bundle pkg ∧
    LipschitzMapCarrier source' target' bound' graph' modulus' transports' routes'
        provenance' localCert' bundle pkg ∧
      hsame source source' ∧ hsame target target' ∧ hsame bound bound' ∧
        hsame graph graph' ∧ hsame modulus modulus' ∧ Cont graph bound modulus ∧
          Cont graph' bound' modulus' ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle provenance' pkg

theorem LipschitzMapCarrier_uniform_modulus_boundary [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont provenance localCert consumer ->
        UnaryHistory modulus ∧ UnaryHistory consumer ∧ Cont graph bound modulus ∧
          Cont modulus routes provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerCont
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed carrier.right.right.right.left carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary carrier.right.right.right.right.right.right.left consumerCont
  exact
    ⟨modulusUnary,
      consumerUnary,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem LipschitzMapCarrier_identity_carrier_boundary [AskSetup] [PackageSetup]
    {source bound graph modulus transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source -> UnaryHistory bound -> UnaryHistory graph -> UnaryHistory transports ->
      UnaryHistory routes -> UnaryHistory localCert -> Cont graph bound modulus ->
        Cont modulus routes provenance -> PkgSig bundle provenance pkg ->
          LipschitzMapCarrier source source bound graph modulus transports routes provenance
              localCert bundle pkg ∧
            UnaryHistory modulus := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro sourceUnary boundUnary graphUnary transportsUnary routesUnary localCertUnary
    graphBoundModulus modulusRoutesProvenance provenancePkg
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  exact
    ⟨⟨sourceUnary, sourceUnary, boundUnary, graphUnary, transportsUnary, routesUnary,
      localCertUnary, graphBoundModulus, modulusRoutesProvenance, provenancePkg⟩,
      modulusUnary⟩

theorem LipschitzMapCarrier_uniform_modulus_consumer_handoff [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont provenance localCert consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory source ∧ UnaryHistory graph ∧ UnaryHistory bound ∧
            UnaryHistory modulus ∧ UnaryHistory consumer ∧ Cont graph bound modulus ∧
              Cont modulus routes provenance ∧ Cont provenance localCert consumer ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨sourceUnary, _targetUnary, boundUnary, graphUnary, _transportsUnary, routesUnary,
    localCertUnary, graphBoundModulus, modulusRoutesProvenance, provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesProvenance
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary localCertUnary consumerRoute
  exact
    ⟨sourceUnary, graphUnary, boundUnary, modulusUnary, consumerUnary, graphBoundModulus,
      modulusRoutesProvenance, consumerRoute, provenancePkg, consumerPkg⟩

theorem LipschitzMapCarrier_bound_transport [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert source' target'
      bound' graph' modulus' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      hsame source source' ->
        hsame target target' ->
          hsame bound bound' ->
            hsame graph graph' ->
              Cont graph' bound' modulus' ->
                LipschitzMapCarrier source' target' bound' graph' modulus' transports routes
                    provenance localCert bundle pkg ∧
                  hsame modulus modulus' := by
  intro carrier sameSource sameTarget sameBound sameGraph modulusCont'
  obtain ⟨sourceUnary, targetUnary, boundUnary, graphUnary, transportsUnary, routesUnary,
    localCertUnary, modulusCont, provenanceCont, pkgSig⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have targetUnary' : UnaryHistory target' :=
    unary_transport targetUnary sameTarget
  have boundUnary' : UnaryHistory bound' :=
    unary_transport boundUnary sameBound
  have graphUnary' : UnaryHistory graph' :=
    unary_transport graphUnary sameGraph
  have _modulusUnary' : UnaryHistory modulus' :=
    unary_cont_closed graphUnary' boundUnary' modulusCont'
  have sameModulus : hsame modulus modulus' :=
    cont_respects_hsame sameGraph sameBound modulusCont modulusCont'
  have provenanceCont' : Cont modulus' routes provenance := by
    cases sameModulus
    exact provenanceCont
  exact
    ⟨⟨sourceUnary', targetUnary', boundUnary', graphUnary', transportsUnary, routesUnary,
      localCertUnary, modulusCont', provenanceCont', pkgSig⟩, sameModulus⟩

theorem LipschitzMapCarrier_composite_bound_routing [AskSetup] [PackageSetup]
    {source middle target bound graph modulus transports routes provenance localCert bound' graph'
      modulus' transports' routes' provenance' localCert' compositeGraph compositeModulus
      compositeProvenance consumer : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    LipschitzMapCarrier source middle bound graph modulus transports routes provenance localCert
        bundle pkg ->
      LipschitzMapCarrier middle target bound' graph' modulus' transports' routes' provenance'
          localCert' bundle' pkg' ->
        Cont graph graph' compositeGraph ->
          Cont modulus modulus' compositeModulus ->
            Cont compositeModulus routes' compositeProvenance ->
              Cont compositeProvenance localCert' consumer ->
                UnaryHistory compositeGraph ∧ UnaryHistory compositeModulus ∧
                  UnaryHistory compositeProvenance ∧ UnaryHistory consumer ∧
                    Cont graph graph' compositeGraph ∧
                      Cont modulus modulus' compositeModulus := by
  intro carrier carrier' graphRoute modulusRoute provenanceRoute consumerRoute
  obtain ⟨_sourceUnary, _middleUnary, boundUnary, graphUnary, _transportsUnary,
    routesUnary, _localCertUnary, modulusCont, _provenanceCont, _pkgSig⟩ := carrier
  obtain ⟨_middleUnary', _targetUnary, boundUnary', graphUnary', _transportsUnary',
    routesUnary', localCertUnary', modulusCont', _provenanceCont', _pkgSig'⟩ := carrier'
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary modulusCont
  have modulusUnary' : UnaryHistory modulus' :=
    unary_cont_closed graphUnary' boundUnary' modulusCont'
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphUnary graphUnary' graphRoute
  have compositeModulusUnary : UnaryHistory compositeModulus :=
    unary_cont_closed modulusUnary modulusUnary' modulusRoute
  have compositeProvenanceUnary : UnaryHistory compositeProvenance :=
    unary_cont_closed compositeModulusUnary routesUnary' provenanceRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed compositeProvenanceUnary localCertUnary' consumerRoute
  exact
    ⟨compositeGraphUnary, compositeModulusUnary, compositeProvenanceUnary, consumerUnary,
      graphRoute, modulusRoute⟩

theorem LipschitzMapCarrier_namecert_obligation_certificate [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      SemanticNameCert
            (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
            (fun row : BHist => hsame row localCert)
            (fun row : BHist => hsame row localCert ∧ Cont modulus routes provenance)
            hsame ∧
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory bound ∧ UnaryHistory graph ∧
          UnaryHistory modulus ∧ Cont graph bound modulus ∧ Cont modulus routes provenance ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  obtain ⟨sourceUnary, targetUnary, boundUnary, graphUnary, _transportsUnary, routesUnary,
    localCertUnary, graphBoundModulus, modulusRoutesProvenance, pkgSig⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have localSource : hsame localCert localCert ∧ UnaryHistory localCert :=
    ⟨hsame_refl localCert, localCertUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
          (fun row : BHist => hsame row localCert)
          (fun row : BHist => hsame row localCert ∧ Cont modulus routes provenance)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localCert localSource
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoutesProvenance⟩
  }
  exact
    ⟨cert, sourceUnary, targetUnary, boundUnary, graphUnary, modulusUnary, graphBoundModulus,
      modulusRoutesProvenance, pkgSig⟩

theorem LipschitzMapCarrier_target_distance_exactness [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert sourceDistance
      targetDistance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont source graph sourceDistance ->
        Cont sourceDistance bound targetDistance ->
          PkgSig bundle targetDistance pkg ->
            UnaryHistory source ∧ UnaryHistory graph ∧ UnaryHistory bound ∧
              UnaryHistory sourceDistance ∧ UnaryHistory targetDistance ∧
                Cont source graph sourceDistance ∧ Cont sourceDistance bound targetDistance ∧
                  Cont graph bound modulus ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle targetDistance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceGraphDistance sourceDistanceBound targetDistancePkg
  obtain ⟨sourceUnary, _targetUnary, boundUnary, graphUnary, _transportsUnary, _routesUnary,
    _localCertUnary, graphBoundModulus, _modulusRoutesProvenance, provenancePkg⟩ := carrier
  have sourceDistanceUnary : UnaryHistory sourceDistance :=
    unary_cont_closed sourceUnary graphUnary sourceGraphDistance
  have targetDistanceUnary : UnaryHistory targetDistance :=
    unary_cont_closed sourceDistanceUnary boundUnary sourceDistanceBound
  exact
    ⟨sourceUnary, graphUnary, boundUnary, sourceDistanceUnary, targetDistanceUnary,
      sourceGraphDistance, sourceDistanceBound, graphBoundModulus, provenancePkg,
      targetDistancePkg⟩

theorem LipschitzMapCarrier_contraction_threshold_handoff [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert threshold handoff :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      UnaryHistory threshold ->
        Cont bound threshold handoff ->
          PkgSig bundle handoff pkg ->
            UnaryHistory bound ∧ UnaryHistory threshold ∧ UnaryHistory handoff ∧
              Cont graph bound modulus ∧ Cont bound threshold handoff ∧
                Cont modulus routes provenance ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier thresholdUnary thresholdRoute handoffPkg
  obtain ⟨_sourceUnary, _targetUnary, boundUnary, _graphUnary, _transportsUnary,
    _routesUnary, _localCertUnary, graphBoundModulus, modulusRoutesProvenance,
    provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed boundUnary thresholdUnary thresholdRoute
  exact
    ⟨boundUnary, thresholdUnary, handoffUnary, graphBoundModulus, thresholdRoute,
      modulusRoutesProvenance, provenancePkg, handoffPkg⟩

theorem LipschitzMapCarrier_contraction_threshold_factorization [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert threshold handoff
      completeRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      UnaryHistory threshold ->
        UnaryHistory completeRow ->
          Cont bound threshold handoff ->
            Cont handoff completeRow consumer ->
              PkgSig bundle consumer pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row bound ∨ hsame row handoff ∨ hsame row completeRow ∨
                        hsame row consumer)
                    (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                    hsame ∧
                  UnaryHistory bound ∧ UnaryHistory threshold ∧ UnaryHistory handoff ∧
                    UnaryHistory completeRow ∧ UnaryHistory consumer ∧
                      Cont graph bound modulus ∧ Cont bound threshold handoff ∧
                        Cont handoff completeRow consumer ∧ Cont modulus routes provenance ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier thresholdUnary completeUnary thresholdRoute consumerRoute consumerPkg
  obtain ⟨_sourceUnary, _targetUnary, boundUnary, _graphUnary, _transportsUnary,
    _routesUnary, _localCertUnary, graphBoundModulus, modulusRoutesProvenance,
    provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed boundUnary thresholdUnary thresholdRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary completeUnary consumerRoute
  have sourceAtConsumer : hsame consumer consumer ∧ UnaryHistory consumer :=
    ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bound ∨ hsame row handoff ∨ hsame row completeRow ∨ hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceAtConsumer
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨cert, boundUnary, thresholdUnary, handoffUnary, completeUnary, consumerUnary,
      graphBoundModulus, thresholdRoute, consumerRoute, modulusRoutesProvenance,
      provenancePkg, consumerPkg⟩

theorem LipschitzMapCarrier_public_modulus_export [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont graph bound publicRead ->
        PkgSig bundle publicRead pkg ->
          hsame publicRead modulus ∧ UnaryHistory modulus ∧ UnaryHistory publicRead ∧
            Cont graph bound modulus ∧ Cont graph bound publicRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨_sourceUnary, _targetUnary, boundUnary, graphUnary, _transportsUnary,
    _routesUnary, _localCertUnary, graphBoundModulus, _modulusRoutesProvenance,
    provenancePkg⟩ := carrier
  have samePublicModulus : hsame publicRead modulus :=
    cont_deterministic publicRoute graphBoundModulus
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed graphUnary boundUnary publicRoute
  exact
    ⟨samePublicModulus, modulusUnary, publicUnary, graphBoundModulus, publicRoute,
      provenancePkg, publicPkg⟩

theorem LipschitzMapCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont provenance localCert consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist => hsame row localCert ∨ hsame row modulus ∨ hsame row consumer)
              (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory bound ∧
              UnaryHistory graph ∧ UnaryHistory modulus ∧ UnaryHistory consumer ∧
                Cont graph bound modulus ∧ Cont modulus routes provenance ∧
                  Cont provenance localCert consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier consumerRoute consumerPkg
  obtain ⟨sourceUnary, targetUnary, boundUnary, graphUnary, _transportsUnary, routesUnary,
    localCertUnary, graphBoundModulus, modulusRoutesProvenance, provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesProvenance
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary localCertUnary consumerRoute
  have sourceAtConsumer : hsame consumer consumer ∧ UnaryHistory consumer :=
    ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist => hsame row localCert ∨ hsame row modulus ∨ hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceAtConsumer
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨cert, sourceUnary, targetUnary, boundUnary, graphUnary, modulusUnary, consumerUnary,
      graphBoundModulus, modulusRoutesProvenance, consumerRoute, provenancePkg, consumerPkg⟩

theorem LipschitzMapCarrier_composition_boundary [AskSetup] [PackageSetup]
    {source middle target bound graph modulus transports routes provenance localCert bound' graph'
      modulus' transports' routes' provenance' localCert' compositeGraph compositeModulus
      compositeProvenance consumer : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    LipschitzMapCarrier source middle bound graph modulus transports routes provenance localCert
        bundle pkg ->
      LipschitzMapCarrier middle target bound' graph' modulus' transports' routes' provenance'
          localCert' bundle' pkg' ->
        Cont graph graph' compositeGraph ->
          Cont modulus modulus' compositeModulus ->
            Cont compositeModulus routes' compositeProvenance ->
              Cont compositeProvenance localCert' consumer ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist => hsame row consumer ∧ Cont graph graph' compositeGraph)
                    (fun row : BHist =>
                      hsame row consumer ∧ Cont compositeProvenance localCert' consumer)
                    hsame ∧
                  UnaryHistory compositeGraph ∧ UnaryHistory compositeModulus ∧
                    UnaryHistory compositeProvenance ∧ UnaryHistory consumer ∧
                      Cont graph graph' compositeGraph ∧
                        Cont modulus modulus' compositeModulus ∧
                          Cont compositeModulus routes' compositeProvenance ∧
                            Cont compositeProvenance localCert' consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier carrier' graphRoute modulusRoute provenanceRoute consumerRoute
  obtain ⟨_sourceUnary, _middleUnary, boundUnary, graphUnary, _transportsUnary,
    _routesUnary, _localCertUnary, graphBoundModulus, _modulusRoutesProvenance, _pkgSig⟩ :=
    carrier
  obtain ⟨_middleUnary', _targetUnary, boundUnary', graphUnary', _transportsUnary',
    routesUnary', localCertUnary', graphBoundModulus', _modulusRoutesProvenance',
    _pkgSig'⟩ := carrier'
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have modulusUnary' : UnaryHistory modulus' :=
    unary_cont_closed graphUnary' boundUnary' graphBoundModulus'
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphUnary graphUnary' graphRoute
  have compositeModulusUnary : UnaryHistory compositeModulus :=
    unary_cont_closed modulusUnary modulusUnary' modulusRoute
  have compositeProvenanceUnary : UnaryHistory compositeProvenance :=
    unary_cont_closed compositeModulusUnary routesUnary' provenanceRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed compositeProvenanceUnary localCertUnary' consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist => hsame row consumer ∧ Cont graph graph' compositeGraph)
          (fun row : BHist =>
            hsame row consumer ∧ Cont compositeProvenance localCert' consumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact ⟨source.left, graphRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, compositeGraphUnary, compositeModulusUnary, compositeProvenanceUnary,
      consumerUnary, graphRoute, modulusRoute, provenanceRoute, consumerRoute⟩

end BEDC.Derived.LipschitzMapUp
