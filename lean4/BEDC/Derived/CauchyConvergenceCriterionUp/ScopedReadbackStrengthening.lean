import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_scoped_readback_strengthening [AskSetup]
    [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      regularRead completionRead nullRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont handoff route regularRead ->
        Cont sealRow route completionRead ->
          Cont schedule modulus nullRead ->
            PkgSig bundle regularRead pkg ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                  UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory regularRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory nullRead ∧
                      Cont schedule modulus dyadic ∧ Cont dyadic handoff sealRow ∧
                        Cont handoff route regularRead ∧ Cont sealRow route completionRead ∧
                          hsame nullRead dyadic ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier handoffRouteRegular sealRouteCompletion scheduleModulusNull _regularPkg
    _completionPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteRegular
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary routeUnary sealRouteCompletion
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusNull
  have sameNullDyadic : hsame nullRead dyadic :=
    cont_deterministic scheduleModulusNull scheduleModulusDyadic
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, regularUnary,
      completionUnary, nullUnary, scheduleModulusDyadic, dyadicHandoffSeal,
      handoffRouteRegular, sealRouteCompletion, sameNullDyadic, provenancePkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
