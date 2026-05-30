import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_regular_tail_window [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      firstTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont dyadic handoff firstTail ->
        PkgSig bundle firstTail pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
            UnaryHistory handoff ∧ UnaryHistory firstTail ∧ Cont schedule modulus dyadic ∧
              Cont dyadic handoff firstTail ∧ Cont dyadic handoff sealRow ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle firstTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier dyadicHandoffFirstTail firstTailPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have firstTailUnary : UnaryHistory firstTail :=
    unary_cont_closed dyadicUnary handoffUnary dyadicHandoffFirstTail
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, firstTailUnary,
      scheduleModulusDyadic, dyadicHandoffFirstTail, dyadicHandoffSeal, provenancePkg,
      firstTailPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
