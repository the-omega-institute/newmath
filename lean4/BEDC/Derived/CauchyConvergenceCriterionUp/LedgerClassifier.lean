import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_ledger_classifier_exactness [AskSetup] [PackageSetup]
    {schedule modulus dyadic dyadicPrime handoff sealRow sealRowPrime transportRow route
      provenance localCert classifierRead classifierReadPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg →
      CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRowPrime
          transportRow route provenance localCert bundle pkg →
        Cont schedule modulus dyadicPrime →
          Cont schedule modulus dyadic →
            Cont dyadic handoff sealRow →
              Cont dyadic handoff sealRowPrime →
                Cont sealRow route classifierRead →
                  Cont sealRowPrime route classifierReadPrime →
                    PkgSig bundle classifierRead pkg →
                      PkgSig bundle classifierReadPrime pkg →
                        hsame dyadicPrime dyadic ∧ hsame sealRow sealRowPrime ∧
                          hsame classifierRead classifierReadPrime ∧
                            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro carrier _carrierPrime scheduleModulusDyadicPrime scheduleModulusDyadic
    dyadicHandoffSeal dyadicHandoffSealPrime sealRouteClassifier sealPrimeRouteClassifier
    _classifierPkg _classifierPrimePkg
  obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _handoffUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _carrierScheduleModulusDyadic, _carrierDyadicHandoffSeal, _sealTransportRoute,
    _routeProvenanceLocal, _sameSealHandoff, _sameSealProvenance, provenancePkg⟩ :=
    carrier
  have sameDyadic : hsame dyadicPrime dyadic :=
    cont_deterministic scheduleModulusDyadicPrime scheduleModulusDyadic
  have sameSeal : hsame sealRow sealRowPrime :=
    cont_deterministic dyadicHandoffSeal dyadicHandoffSealPrime
  have sameClassifier : hsame classifierRead classifierReadPrime := by
    cases sameSeal
    exact cont_deterministic sealRouteClassifier sealPrimeRouteClassifier
  exact ⟨sameDyadic, sameSeal, sameClassifier, provenancePkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
