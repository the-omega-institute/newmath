import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CollisionKernelSpectrumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CollisionKernelSpectrumUp
