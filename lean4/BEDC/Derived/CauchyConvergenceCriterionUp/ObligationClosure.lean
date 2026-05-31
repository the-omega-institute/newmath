import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_obligation_closure_upgrade [AskSetup]
    [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      completionRead nullRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont sealRow route completionRead ->
        Cont handoff route nullRead ->
          PkgSig bundle completionRead pkg ->
            PkgSig bundle nullRead pkg ->
              UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory completionRead ∧
                  UnaryHistory nullRead ∧ Cont schedule modulus dyadic ∧
                    Cont dyadic handoff sealRow ∧ Cont sealRow route completionRead ∧
                      Cont handoff route nullRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle completionRead pkg ∧ PkgSig bundle nullRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sealCompletion handoffNull completionPkg nullPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    scheduleModulusDyadic, dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal,
    _sameSealHandoff, _sameSealProvenance, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary routeUnary sealCompletion
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed handoffUnary routeUnary handoffNull
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, completionUnary,
      nullUnary, scheduleModulusDyadic, dyadicHandoffSeal, sealCompletion, handoffNull,
      provenancePkg, completionPkg, nullPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
