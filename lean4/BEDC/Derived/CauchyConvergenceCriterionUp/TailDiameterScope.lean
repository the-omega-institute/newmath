import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_tail_diameter_scope [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont handoff route tailRead ->
        PkgSig bundle tailRead pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
            UnaryHistory handoff ∧ UnaryHistory tailRead ∧
              Cont schedule modulus dyadic ∧ Cont dyadic handoff sealRow ∧
                Cont handoff route tailRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier handoffRouteTail tailPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, _sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteTail
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, tailUnary, scheduleModulusDyadic,
      dyadicHandoffSeal, handoffRouteTail, provenancePkg, tailPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
