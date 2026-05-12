import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CollisionKernelSpectrumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CollisionKernelSpectrumCarrier [AskSetup] [PackageSetup]
    (golden fold fiber moment kernel shadow handoff transport provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory golden ∧ UnaryHistory fold ∧ UnaryHistory fiber ∧ UnaryHistory moment ∧
    UnaryHistory kernel ∧ UnaryHistory shadow ∧ UnaryHistory handoff ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont golden fold fiber ∧ Cont fiber moment kernel ∧ Cont kernel handoff shadow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem CollisionKernelSpectrumCarrier_finite_window_spectral_shadow [AskSetup] [PackageSetup]
    {golden fold fiber moment kernel shadow handoff transport provenance nameCert golden'
      fold' fiber' moment' kernel' shadow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff transport
        provenance nameCert bundle pkg ->
      hsame golden golden' ->
        hsame fold fold' ->
          hsame fiber fiber' ->
            hsame moment moment' ->
              Cont golden' fold' fiber' ->
                Cont fiber' moment' kernel' ->
                  Cont kernel' handoff shadow' ->
                    hsame kernel kernel' ∧ hsame shadow shadow' ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameGolden sameFold sameFiber sameMoment goldenRoute fiberRoute shadowRoute
  obtain ⟨_goldenUnary, _foldUnary, _fiberUnary, _momentUnary, _kernelUnary, _shadowUnary,
    _handoffUnary, _transportUnary, _provenanceUnary, _nameCertUnary, oldGoldenRoute,
    oldFiberRoute, oldShadowRoute, provenancePkg, _nameCertPkg⟩ := carrier
  have sameKernel : hsame kernel kernel' :=
    cont_respects_hsame sameFiber sameMoment oldFiberRoute fiberRoute
  have sameShadow : hsame shadow shadow' :=
    cont_respects_hsame sameKernel (hsame_refl handoff) oldShadowRoute shadowRoute
  exact ⟨sameKernel, sameShadow, provenancePkg⟩

theorem CollisionKernelSpectrumCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {golden fold fiber moment kernel shadow handoff transport provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff transport
        provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row kernel ∧
            CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff
              transport provenance nameCert bundle pkg)
        (fun row : BHist => hsame row kernel)
        (fun row : BHist => hsame row kernel ∧ PkgSig bundle provenance pkg)
        hsame ∧ UnaryHistory golden ∧ UnaryHistory kernel ∧ UnaryHistory shadow ∧
          Cont fiber moment kernel ∧ Cont kernel handoff shadow ∧
            PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont NameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨goldenUnary, _foldUnary, _fiberUnary, _momentUnary, kernelUnary, shadowUnary,
    _handoffUnary, _transportUnary, _provenanceUnary, _nameCertUnary, _goldenFoldFiber,
    fiberMomentKernel, kernelHandoffShadow, provenancePkg, nameCertPkg⟩ := carrier
  have sourceWitness :
      (fun row : BHist =>
        hsame row kernel ∧
          CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff
            transport provenance nameCert bundle pkg) kernel := by
    exact And.intro (hsame_refl kernel) carrierWitness
  have core :
      NameCert
        (fun row : BHist =>
          hsame row kernel ∧
            CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff
              transport provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro kernel sourceWitness
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameKKernel : hsame k kernel :=
          hsame_trans (hsame_symm sameHK) sourceH.left
        exact And.intro sameKKernel sourceH.right
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row kernel ∧
            CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff
              transport provenance nameCert bundle pkg)
        (fun row : BHist => hsame row kernel)
        (fun row : BHist => hsame row kernel ∧ PkgSig bundle provenance pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro h source
        exact source.left
      ledger_sound := by
        intro h source
        exact And.intro source.left provenancePkg
    }
  exact
    And.intro cert
      (And.intro goldenUnary
        (And.intro kernelUnary
          (And.intro shadowUnary
            (And.intro fiberMomentKernel
              (And.intro kernelHandoffShadow nameCertPkg)))))

theorem CollisionKernelSpectrumCarrier_ledger_non_escape [AskSetup] [PackageSetup]
    {golden fold fiber moment kernel shadow handoff transport provenance nameCert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff transport
        provenance nameCert bundle pkg ->
      Cont shadow transport consumer ->
        UnaryHistory consumer ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier consumerRoute
  obtain ⟨_goldenUnary, _foldUnary, _fiberUnary, _momentUnary, _kernelUnary, shadowUnary,
    _handoffUnary, transportUnary, _provenanceUnary, _nameCertUnary, _goldenFoldFiber,
    _fiberMomentKernel, _kernelHandoffShadow, provenancePkg, nameCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed shadowUnary transportUnary consumerRoute
  exact ⟨consumerUnary, provenancePkg, nameCertPkg⟩

theorem CollisionKernelSpectrumCarrier_adjacency_moment_handoff [AskSetup] [PackageSetup]
    {golden fold fiber moment kernel shadow handoff transport provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff transport
        provenance nameCert bundle pkg ->
      exists adjacencyMoment : BHist,
        UnaryHistory adjacencyMoment ∧ hsame adjacencyMoment (append golden moment) ∧
          Cont golden fold fiber ∧ Cont fiber moment kernel ∧ Cont kernel handoff shadow ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨goldenUnary, _foldUnary, _fiberUnary, momentUnary, _kernelUnary, _shadowUnary,
    _handoffUnary, _transportUnary, _provenanceUnary, _nameCertUnary, goldenFoldFiber,
    fiberMomentKernel, kernelHandoffShadow, provenancePkg, nameCertPkg⟩ := carrier
  exact
    ⟨append golden moment, unary_append_closed goldenUnary momentUnary, hsame_refl _,
      goldenFoldFiber, fiberMomentKernel, kernelHandoffShadow, provenancePkg, nameCertPkg⟩

theorem CollisionKernelSpectrumCarrier_moment_index_projection [AskSetup] [PackageSetup]
    {golden fold fiber moment kernel shadow handoff transport provenance nameCert consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff transport
        provenance nameCert bundle pkg ->
      Cont moment kernel consumer ->
        UnaryHistory moment ∧ UnaryHistory kernel ∧ UnaryHistory consumer ∧
          Cont fiber moment kernel ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier momentKernelConsumer
  obtain ⟨_goldenUnary, _foldUnary, _fiberUnary, momentUnary, kernelUnary, _shadowUnary,
    _handoffUnary, _transportUnary, _provenanceUnary, _nameCertUnary, _goldenFoldFiber,
    fiberMomentKernel, _kernelHandoffShadow, provenancePkg, nameCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed momentUnary kernelUnary momentKernelConsumer
  exact
    ⟨momentUnary, kernelUnary, consumerUnary, fiberMomentKernel, provenancePkg, nameCertPkg⟩

theorem CollisionKernelSpectrumCarrier_window_restriction [AskSetup] [PackageSetup]
    {golden fold fiber moment kernel shadow handoff transport provenance nameCert goldenSmall
      fiberSmall kernelSmall shadowSmall : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelSpectrumCarrier golden fold fiber moment kernel shadow handoff transport
        provenance nameCert bundle pkg ->
      hsame goldenSmall golden ->
        Cont goldenSmall fold fiberSmall ->
          Cont fiberSmall moment kernelSmall ->
            Cont kernelSmall handoff shadowSmall ->
              CollisionKernelSpectrumCarrier goldenSmall fold fiberSmall moment kernelSmall
                  shadowSmall handoff transport provenance nameCert bundle pkg ∧
                hsame kernel kernelSmall ∧ hsame shadow shadowSmall := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameGoldenSmall goldenSmallFoldFiberSmall fiberSmallMomentKernelSmall
    kernelSmallHandoffShadowSmall
  obtain ⟨goldenUnary, foldUnary, _fiberUnary, momentUnary, _kernelUnary, _shadowUnary,
    handoffUnary, transportUnary, provenanceUnary, nameCertUnary, goldenFoldFiber,
    fiberMomentKernel, kernelHandoffShadow, provenancePkg, nameCertPkg⟩ := carrier
  have goldenSmallUnary : UnaryHistory goldenSmall :=
    unary_transport goldenUnary (hsame_symm sameGoldenSmall)
  have fiberSmallUnary : UnaryHistory fiberSmall :=
    unary_cont_closed goldenSmallUnary foldUnary goldenSmallFoldFiberSmall
  have kernelSmallUnary : UnaryHistory kernelSmall :=
    unary_cont_closed fiberSmallUnary momentUnary fiberSmallMomentKernelSmall
  have shadowSmallUnary : UnaryHistory shadowSmall :=
    unary_cont_closed kernelSmallUnary handoffUnary kernelSmallHandoffShadowSmall
  have sameFiber : hsame fiber fiberSmall :=
    cont_respects_hsame (hsame_symm sameGoldenSmall) (hsame_refl fold) goldenFoldFiber
      goldenSmallFoldFiberSmall
  have sameKernel : hsame kernel kernelSmall :=
    cont_respects_hsame sameFiber (hsame_refl moment) fiberMomentKernel
      fiberSmallMomentKernelSmall
  have sameShadow : hsame shadow shadowSmall :=
    cont_respects_hsame sameKernel (hsame_refl handoff) kernelHandoffShadow
      kernelSmallHandoffShadowSmall
  have restricted :
      CollisionKernelSpectrumCarrier goldenSmall fold fiberSmall moment kernelSmall shadowSmall
          handoff transport provenance nameCert bundle pkg :=
    ⟨goldenSmallUnary, foldUnary, fiberSmallUnary, momentUnary, kernelSmallUnary,
      shadowSmallUnary, handoffUnary, transportUnary, provenanceUnary, nameCertUnary,
      goldenSmallFoldFiberSmall, fiberSmallMomentKernelSmall, kernelSmallHandoffShadowSmall,
      provenancePkg, nameCertPkg⟩
  exact ⟨restricted, sameKernel, sameShadow⟩

end BEDC.Derived.CollisionKernelSpectrumUp
