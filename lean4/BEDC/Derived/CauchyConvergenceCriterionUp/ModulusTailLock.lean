import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_modulus_tail_lock [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert nullRoute
      tailLock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow route
        provenance localCert bundle pkg ->
      Cont dyadic handoff nullRoute ->
        Cont nullRoute sealRow tailLock ->
          PkgSig bundle tailLock pkg ->
            UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
              UnaryHistory handoff ∧ UnaryHistory nullRoute ∧ UnaryHistory tailLock ∧
                Cont dyadic handoff nullRoute ∧ Cont nullRoute sealRow tailLock ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle tailLock pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier dyadicHandoffNull nullSealTail tailPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _scheduleModulusDyadic,
    _dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have nullUnary : UnaryHistory nullRoute :=
    unary_cont_closed dyadicUnary handoffUnary dyadicHandoffNull
  have tailUnary : UnaryHistory tailLock :=
    unary_cont_closed nullUnary sealUnary nullSealTail
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, nullUnary, tailUnary,
      dyadicHandoffNull, nullSealTail, provenancePkg, tailPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
