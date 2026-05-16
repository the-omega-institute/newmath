import BEDC.Derived.CauchyModulusExtractionUp
import BEDC.Derived.CauchyModulusMeetUp
import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_shared_modulus_handoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tolerance budget exWindows schedule modulus exDyadic exTransport exRoute exProvenance
      exCert s0 s1 mu0 mu1 mu h c p n extractedConsumer terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      BEDC.Derived.CauchyModulusExtractionUp.CauchyModulusExtractionCarrier
          tolerance budget exWindows schedule modulus exDyadic exTransport exRoute
          exProvenance exCert bundle pkg →
        BEDC.Derived.CauchyModulusMeetUp.CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n
            bundle pkg →
          Cont schedule exDyadic extractedConsumer →
            Cont extractedConsumer mu terminal →
              PkgSig bundle extractedConsumer pkg →
                PkgSig bundle terminal pkg →
                  UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                    UnaryHistory schedule ∧ UnaryHistory exDyadic ∧
                      UnaryHistory extractedConsumer ∧ UnaryHistory mu ∧
                        UnaryHistory terminal ∧ Cont dyadic windows readback ∧
                          Cont schedule exDyadic extractedConsumer ∧
                            Cont extractedConsumer mu terminal ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle exProvenance pkg ∧ PkgSig bundle p pkg ∧
                                  PkgSig bundle extractedConsumer pkg ∧
                                    PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro diagonalCarrier extractionCarrier meetPacket scheduleExtractedConsumer
    extractedConsumerTerminal extractedConsumerPkg terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨_toleranceUnary, _budgetUnary, _exWindowsUnary, scheduleUnary, _modulusUnary,
    exDyadicUnary, _exTransportUnary, _exRouteUnary, _exProvenanceUnary, _exCertUnary,
    _toleranceBudgetWindows, _windowsScheduleModulus, _modulusDyadicTransport,
    _transportRouteProvenance, exProvenancePkg⟩ := extractionCarrier
  obtain ⟨_s0Unary, _s1Unary, _mu0Unary, _mu1Unary, muUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _s0Mu0H, _s1Mu1C, _hCMu, _samePN, pPkg⟩ := meetPacket
  have extractedConsumerUnary : UnaryHistory extractedConsumer :=
    unary_cont_closed scheduleUnary exDyadicUnary scheduleExtractedConsumer
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed extractedConsumerUnary muUnary extractedConsumerTerminal
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, scheduleUnary, exDyadicUnary,
      extractedConsumerUnary, muUnary, terminalUnary, dyadicWindowsReadback,
      scheduleExtractedConsumer, extractedConsumerTerminal, provenancePkg, exProvenancePkg,
      pPkg, extractedConsumerPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
