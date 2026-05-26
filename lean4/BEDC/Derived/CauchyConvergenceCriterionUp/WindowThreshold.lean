import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionDyadicRoute_determinacy [AskSetup] [PackageSetup]
    {schedule modulus dyadic dyadic' handoff sealRow transportRow route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg →
      Cont schedule modulus dyadic' →
        hsame dyadic dyadic' ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro carrier alternateRoute
  obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _handoffUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    scheduleModulusDyadic, _dyadicHandoffSeal, _sealTransportRoute,
    _routeProvenanceLocal, _sameSealHandoff, _sameSealProvenance, provenancePkg⟩ :=
    carrier
  exact And.intro (cont_deterministic scheduleModulusDyadic alternateRoute) provenancePkg

end BEDC.Derived.CauchyConvergenceCriterionUp
