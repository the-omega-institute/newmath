import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_kernel_dependency_scope [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont schedule modulus kernelRead ->
        Cont kernelRead dyadic handoff ->
          PkgSig bundle kernelRead pkg ->
            UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
              UnaryHistory handoff ∧ UnaryHistory kernelRead ∧
                Cont schedule modulus kernelRead ∧ Cont kernelRead dyadic handoff ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle kernelRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier scheduleModulusKernel kernelDyadicHandoff kernelPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _scheduleModulusDyadic, _dyadicHandoffSeal, _sealTransportRoute,
    _routeProvenanceLocal, _sameSealHandoff, _sameSealProvenance, provenancePkg⟩ :=
      carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusKernel
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, kernelUnary,
      scheduleModulusKernel, kernelDyadicHandoff, provenancePkg, kernelPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
