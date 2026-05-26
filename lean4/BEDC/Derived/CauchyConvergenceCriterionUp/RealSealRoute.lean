import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_real_seal_route [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont handoff route regularRead ->
        Cont regularRead sealRow realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
              UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory regularRead ∧
                UnaryHistory realRead ∧ Cont schedule modulus dyadic ∧
                  Cont dyadic handoff sealRow ∧ Cont handoff route regularRead ∧
                    Cont regularRead sealRow realRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier handoffRouteRegular regularSealReal realPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary sealUnary regularSealReal
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, regularUnary,
      realUnary, scheduleModulusDyadic, dyadicHandoffSeal, handoffRouteRegular,
      regularSealReal, provenancePkg, realPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
