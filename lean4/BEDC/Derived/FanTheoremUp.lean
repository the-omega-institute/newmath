import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FanTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FanTheoremPacket [AskSetup] [PackageSetup]
    (tree bar depth window transport traversal provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tree ∧ UnaryHistory bar ∧ UnaryHistory depth ∧ UnaryHistory window ∧
    UnaryHistory transport ∧ UnaryHistory traversal ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ UnaryHistory endpoint ∧ Cont tree bar depth ∧
        Cont depth window endpoint ∧ Cont transport traversal provenance ∧
          PkgSig bundle endpoint pkg

def FanTheoremPacket_bar_classifier [AskSetup] [PackageSetup]
    (tree bar depth window transport traversal provenance nameCert endpoint tree' bar'
      depth' window' transport' traversal' provenance' nameCert' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont PkgSig
  FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
      bundle pkg ∧
    FanTheoremPacket tree' bar' depth' window' transport' traversal' provenance' nameCert'
      endpoint' bundle pkg ∧
      hsame tree tree' ∧ hsame bar bar' ∧ hsame depth depth' ∧
        hsame window window' ∧ hsame transport transport' ∧ hsame traversal traversal' ∧
          hsame provenance provenance' ∧ hsame nameCert nameCert' ∧
      hsame endpoint endpoint' ∧ Cont tree bar depth ∧ Cont tree' bar' depth' ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle endpoint' pkg

def FanTheoremBarClassifier [AskSetup] [PackageSetup]
    (tree bar depth window transport traversal provenance nameCert endpoint tree' bar' depth'
      window' transport' traversal' provenance' nameCert' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
      bundle pkg ∧
    FanTheoremPacket tree' bar' depth' window' transport' traversal' provenance' nameCert'
        endpoint' bundle pkg ∧
      hsame tree tree' ∧ hsame bar bar' ∧ hsame depth depth' ∧
        hsame window window' ∧ hsame endpoint endpoint' ∧ Cont tree bar depth ∧
          Cont depth window endpoint ∧ PkgSig bundle endpoint pkg

theorem FanTheoremPacket_finite_bar_handoff [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      UnaryHistory tree ∧ UnaryHistory bar ∧ UnaryHistory depth ∧ UnaryHistory window ∧
        UnaryHistory traversal ∧ UnaryHistory provenance ∧ Cont tree bar depth ∧
          Cont depth window endpoint ∧ Cont transport traversal provenance ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨treeUnary, barUnary, depthUnary, windowUnary, _transportUnary, traversalUnary,
    provenanceUnary, _nameCertUnary, _endpointUnary, treeBarDepth, depthWindowEndpoint,
    transportTraversalProvenance, endpointPkg⟩ := packet
  exact
    ⟨treeUnary, barUnary, depthUnary, windowUnary, traversalUnary, provenanceUnary,
      treeBarDepth, depthWindowEndpoint, transportTraversalProvenance, endpointPkg⟩

theorem FanTheoremPacket_namecert_obligations [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              FanTheoremPacket tree bar depth window transport traversal provenance nameCert
                endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory tree ∧ UnaryHistory bar ∧ UnaryHistory depth ∧ UnaryHistory window ∧
          Cont tree bar depth ∧ Cont depth window endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨treeUnary, barUnary, depthUnary, windowUnary, _transportUnary, _traversalUnary,
    _provenanceUnary, _nameCertUnary, _endpointUnary, treeBarDepth, depthWindowEndpoint,
    _transportTraversalProvenance, endpointPkg⟩ := packet
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
            bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, packetWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
              bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              FanTheoremPacket tree bar depth window transport traversal provenance nameCert
                endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
    }
  exact
    ⟨cert, treeUnary, barUnary, depthUnary, windowUnary, treeBarDepth, depthWindowEndpoint,
      endpointPkg⟩

theorem FanTheoremPacket_real_completion_boundary [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      Cont endpoint provenance realConsumer ->
        PkgSig bundle realConsumer pkg ->
          UnaryHistory endpoint ∧ UnaryHistory realConsumer ∧ Cont tree bar depth ∧
            Cont depth window endpoint ∧ Cont endpoint provenance realConsumer ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle realConsumer pkg := by
  intro packet endpointProvenanceRealConsumer realConsumerPkg
  obtain ⟨_treeUnary, _barUnary, _depthUnary, _windowUnary, _transportUnary,
    _traversalUnary, provenanceUnary, _nameCertUnary, endpointUnary, treeBarDepth,
    depthWindowEndpoint, _transportTraversalProvenance, endpointPkg⟩ := packet
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed endpointUnary provenanceUnary endpointProvenanceRealConsumer
  exact
    ⟨endpointUnary, realConsumerUnary, treeBarDepth, depthWindowEndpoint,
      endpointProvenanceRealConsumer, endpointPkg, realConsumerPkg⟩

theorem FanTheoremPacket_bar_uniform_modulus [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint
      modulusConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      Cont window provenance modulusConsumer ->
        PkgSig bundle modulusConsumer pkg ->
          UnaryHistory depth ∧ UnaryHistory window ∧ UnaryHistory provenance ∧
            UnaryHistory modulusConsumer ∧ Cont tree bar depth ∧
              Cont depth window endpoint ∧ Cont window provenance modulusConsumer ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle modulusConsumer pkg := by
  intro packet windowProvenanceModulusConsumer modulusConsumerPkg
  obtain ⟨_treeUnary, _barUnary, depthUnary, windowUnary, _transportUnary,
    _traversalUnary, provenanceUnary, _nameCertUnary, _endpointUnary, treeBarDepth,
    depthWindowEndpoint, _transportTraversalProvenance, endpointPkg⟩ := packet
  have modulusConsumerUnary : UnaryHistory modulusConsumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceModulusConsumer
  exact
    ⟨depthUnary, windowUnary, provenanceUnary, modulusConsumerUnary, treeBarDepth,
      depthWindowEndpoint, windowProvenanceModulusConsumer, endpointPkg, modulusConsumerPkg⟩

theorem FanTheoremPacket_public_uniform_bar_export [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint
      modulusConsumer realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      Cont window provenance modulusConsumer ->
        PkgSig bundle modulusConsumer pkg ->
          Cont endpoint provenance realConsumer ->
            PkgSig bundle realConsumer pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row endpoint ∧
                      FanTheoremPacket tree bar depth window transport traversal provenance
                        nameCert endpoint bundle pkg ∧
                        Cont window provenance modulusConsumer ∧
                          Cont endpoint provenance realConsumer)
                  (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                  (fun row : BHist =>
                    hsame row endpoint ∧ PkgSig bundle modulusConsumer pkg ∧
                      PkgSig bundle realConsumer pkg)
                  hsame ∧
                UnaryHistory modulusConsumer ∧ UnaryHistory realConsumer ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle modulusConsumer pkg ∧
                    PkgSig bundle realConsumer pkg := by
  intro packet windowProvenanceModulusConsumer modulusConsumerPkg
    endpointProvenanceRealConsumer realConsumerPkg
  have packetWitness := packet
  obtain ⟨_treeUnary, _barUnary, _depthUnary, windowUnary, _transportUnary,
    _traversalUnary, provenanceUnary, _nameCertUnary, endpointUnary, _treeBarDepth,
    _depthWindowEndpoint, _transportTraversalProvenance, endpointPkg⟩ := packet
  have modulusConsumerUnary : UnaryHistory modulusConsumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceModulusConsumer
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed endpointUnary provenanceUnary endpointProvenanceRealConsumer
  have endpointSource :
      (fun row : BHist =>
        hsame row endpoint ∧
          FanTheoremPacket tree bar depth window transport traversal provenance nameCert
            endpoint bundle pkg ∧
            Cont window provenance modulusConsumer ∧ Cont endpoint provenance realConsumer)
        endpoint := by
    exact
      ⟨hsame_refl endpoint, packetWitness, windowProvenanceModulusConsumer,
        endpointProvenanceRealConsumer⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            FanTheoremPacket tree bar depth window transport traversal provenance nameCert
              endpoint bundle pkg ∧
              Cont window provenance modulusConsumer ∧ Cont endpoint provenance realConsumer)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left, source.right.left,
            source.right.right.left, source.right.right.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              FanTheoremPacket tree bar depth window transport traversal provenance nameCert
                endpoint bundle pkg ∧
                Cont window provenance modulusConsumer ∧ Cont endpoint provenance realConsumer)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ PkgSig bundle modulusConsumer pkg ∧
              PkgSig bundle realConsumer pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, modulusConsumerPkg, realConsumerPkg⟩
    }
  exact
    ⟨cert, modulusConsumerUnary, realConsumerUnary, endpointPkg, modulusConsumerPkg,
      realConsumerPkg⟩

theorem FanTheoremPacket_compact_uniform_continuity_obligation_surface
    [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint modulusConsumer
      realConsumer compactCoverage pointwiseModulus uniformLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      Cont window provenance modulusConsumer ->
        Cont endpoint provenance realConsumer ->
          Cont modulusConsumer realConsumer compactCoverage ->
            Cont compactCoverage provenance pointwiseModulus ->
              Cont pointwiseModulus endpoint uniformLedger ->
                PkgSig bundle modulusConsumer pkg ->
                  PkgSig bundle realConsumer pkg ->
                    PkgSig bundle compactCoverage pkg ->
                      PkgSig bundle pointwiseModulus pkg ->
                        PkgSig bundle uniformLedger pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row endpoint ∧
                                  FanTheoremPacket tree bar depth window transport traversal
                                    provenance nameCert endpoint bundle pkg ∧
                                    Cont modulusConsumer realConsumer compactCoverage ∧
                                      Cont compactCoverage provenance pointwiseModulus ∧
                                        Cont pointwiseModulus endpoint uniformLedger)
                              (fun row : BHist =>
                                hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                              (fun row : BHist =>
                                hsame row endpoint ∧ PkgSig bundle compactCoverage pkg ∧
                                  PkgSig bundle pointwiseModulus pkg ∧
                                    PkgSig bundle uniformLedger pkg)
                              hsame ∧
                            UnaryHistory compactCoverage ∧ UnaryHistory pointwiseModulus ∧
                              UnaryHistory uniformLedger ∧
                                Cont modulusConsumer realConsumer compactCoverage ∧
                                  Cont compactCoverage provenance pointwiseModulus ∧
                                    Cont pointwiseModulus endpoint uniformLedger ∧
                                      PkgSig bundle uniformLedger pkg := by
  intro packet windowProvenanceModulus endpointProvenanceReal modulusRealCompact
    compactProvenancePointwise pointwiseEndpointUniform modulusPkg realPkg compactPkg
    pointwisePkg uniformPkg
  have packetWitness := packet
  obtain ⟨_treeUnary, _barUnary, _depthUnary, windowUnary, _transportUnary,
    _traversalUnary, provenanceUnary, _nameCertUnary, endpointUnary, _treeBarDepth,
    _depthWindowEndpoint, _transportTraversalProvenance, endpointPkg⟩ := packet
  have modulusUnary : UnaryHistory modulusConsumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceModulus
  have realUnary : UnaryHistory realConsumer :=
    unary_cont_closed endpointUnary provenanceUnary endpointProvenanceReal
  have compactUnary : UnaryHistory compactCoverage :=
    unary_cont_closed modulusUnary realUnary modulusRealCompact
  have pointwiseUnary : UnaryHistory pointwiseModulus :=
    unary_cont_closed compactUnary provenanceUnary compactProvenancePointwise
  have uniformUnary : UnaryHistory uniformLedger :=
    unary_cont_closed pointwiseUnary endpointUnary pointwiseEndpointUniform
  have endpointSource :
      (fun row : BHist =>
        hsame row endpoint ∧
          FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
            bundle pkg ∧
            Cont modulusConsumer realConsumer compactCoverage ∧
              Cont compactCoverage provenance pointwiseModulus ∧
                Cont pointwiseModulus endpoint uniformLedger) endpoint := by
    exact
      ⟨hsame_refl endpoint, packetWitness, modulusRealCompact, compactProvenancePointwise,
        pointwiseEndpointUniform⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            FanTheoremPacket tree bar depth window transport traversal provenance nameCert
              endpoint bundle pkg ∧
              Cont modulusConsumer realConsumer compactCoverage ∧
                Cont compactCoverage provenance pointwiseModulus ∧
                  Cont pointwiseModulus endpoint uniformLedger)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left, source.right.left,
            source.right.right.left, source.right.right.right.left,
            source.right.right.right.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              FanTheoremPacket tree bar depth window transport traversal provenance nameCert
                endpoint bundle pkg ∧
                Cont modulusConsumer realConsumer compactCoverage ∧
                  Cont compactCoverage provenance pointwiseModulus ∧
                    Cont pointwiseModulus endpoint uniformLedger)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ PkgSig bundle compactCoverage pkg ∧
              PkgSig bundle pointwiseModulus pkg ∧ PkgSig bundle uniformLedger pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, compactPkg, pointwisePkg, uniformPkg⟩
    }
  exact
    ⟨cert, compactUnary, pointwiseUnary, uniformUnary, modulusRealCompact,
      compactProvenancePointwise, pointwiseEndpointUniform, uniformPkg⟩

theorem FanTheoremPacket_standard_finite_fan_bridge [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint standardSpread
      standardBar standardDepth bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      hsame tree standardSpread ->
        hsame bar standardBar ->
          hsame depth standardDepth ->
            Cont standardSpread standardBar standardDepth ->
              Cont standardDepth window bridge ->
                PkgSig bundle bridge pkg ->
                  hsame endpoint bridge ∧ UnaryHistory standardSpread ∧
                    UnaryHistory standardBar ∧ UnaryHistory standardDepth ∧
                      UnaryHistory bridge ∧ Cont standardSpread standardBar standardDepth ∧
                        Cont standardDepth window bridge ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle bridge pkg := by
  intro packet sameSpread sameBar sameDepth standardSpreadBarDepth standardDepthWindowBridge
    bridgePkg
  obtain ⟨treeUnary, barUnary, depthUnary, windowUnary, _transportUnary, _traversalUnary,
    _provenanceUnary, _nameCertUnary, _endpointUnary, _treeBarDepth, depthWindowEndpoint,
    _transportTraversalProvenance, endpointPkg⟩ := packet
  have spreadUnary : UnaryHistory standardSpread :=
    unary_transport treeUnary sameSpread
  have standardBarUnary : UnaryHistory standardBar :=
    unary_transport barUnary sameBar
  have standardDepthUnary : UnaryHistory standardDepth :=
    unary_transport depthUnary sameDepth
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed standardDepthUnary windowUnary standardDepthWindowBridge
  have sameEndpointBridge : hsame endpoint bridge := by
    cases sameDepth
    cases depthWindowEndpoint
    cases standardDepthWindowBridge
    rfl
  exact
    ⟨sameEndpointBridge, spreadUnary, standardBarUnary, standardDepthUnary, bridgeUnary,
      standardSpreadBarDepth, standardDepthWindowBridge, endpointPkg, bridgePkg⟩

end BEDC.Derived.FanTheoremUp
