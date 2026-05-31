import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_regular_tail_coverage [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      regularRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont handoff route regularRead ->
        Cont sealRow route completionRead ->
          PkgSig bundle regularRead pkg ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory regularRead ∧
                  UnaryHistory completionRead ∧ Cont schedule modulus dyadic ∧
                    Cont dyadic handoff sealRow ∧ Cont handoff route regularRead ∧
                      Cont sealRow route completionRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle regularRead pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier regularRoute completionRoute regularPkg completionPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed handoffUnary routeUnary regularRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary routeUnary completionRoute
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, regularUnary,
      completionUnary, scheduleModulusDyadic, dyadicHandoffSeal, regularRoute,
      completionRoute, provenancePkg, regularPkg, completionPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
