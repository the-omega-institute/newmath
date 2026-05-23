import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont sealRow route completionRead ->
        PkgSig bundle completionRead pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
            UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory completionRead ∧
              Cont schedule modulus dyadic ∧ Cont dyadic handoff sealRow ∧
                Cont sealRow route completionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sealCompletion completionPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary routeUnary sealCompletion
  exact
    ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, completionUnary,
      scheduleModulusDyadic, dyadicHandoffSeal, sealCompletion, provenancePkg, completionPkg⟩

theorem CauchyConvergenceCriterionCarrier_limit_seal_determinacy [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow sealRowPrime transportRow route provenance localCert
      completionRead completionReadPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRowPrime
          transportRow route provenance localCert bundle pkg ->
        Cont sealRow route completionRead ->
          Cont sealRowPrime route completionReadPrime ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle completionReadPrime pkg ->
                hsame sealRow sealRowPrime ->
                  hsame completionRead completionReadPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier carrierPrime sealCompletion sealPrimeCompletion _completionPkg
    _completionPrimePkg sameSeal
  obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _handoffUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _scheduleModulusDyadic, _dyadicHandoffSeal, _sealTransportRoute,
    _routeProvenanceLocal, _sameSealHandoff, _sameSealProvenance,
    _provenancePkg⟩ := carrier
  obtain ⟨_scheduleUnaryPrime, _modulusUnaryPrime, _dyadicUnaryPrime, _handoffUnaryPrime,
    _sealUnaryPrime, _transportUnaryPrime, _routeUnaryPrime, _provenanceUnaryPrime,
    _localCertUnaryPrime, _scheduleModulusDyadicPrime, _dyadicHandoffSealPrime,
    _sealTransportRoutePrime, _routeProvenanceLocalPrime, _sameSealHandoffPrime,
    _sameSealProvenancePrime, _provenancePkgPrime⟩ := carrierPrime
  cases sameSeal
  exact cont_deterministic sealCompletion sealPrimeCompletion

end BEDC.Derived.CauchyConvergenceCriterionUp
