import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_source_triad_exhaustion [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
        UnaryHistory handoff ∧ UnaryHistory sealRow ∧ Cont schedule modulus dyadic ∧
          Cont dyadic handoff sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, scheduleModulusDyadic,
      dyadicHandoffSeal, provenancePkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
