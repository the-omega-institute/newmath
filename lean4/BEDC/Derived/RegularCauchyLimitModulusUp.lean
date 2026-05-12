import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitModulusPacket [AskSetup] [PackageSetup]
    (input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory modulus ∧ UnaryHistory precision ∧
    UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont input modulus threshold ∧
      Cont threshold precision window ∧ Cont window readback dyadicLedger ∧
        Cont dyadicLedger sealRow cert ∧ PkgSig bundle provenance pkg

theorem RegularCauchyLimitModulusPacket_classifier_transport_exactness [AskSetup] [PackageSetup]
    {input modulus precision threshold window readback dyadicLedger sealRow provenance cert
      threshold' window' dyadicLedger' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitModulusPacket input modulus precision threshold window readback
        dyadicLedger sealRow provenance cert bundle pkg ->
      hsame threshold threshold' ->
        Cont input modulus threshold' ->
          Cont threshold' precision window' ->
            Cont window' readback dyadicLedger' ->
              Cont dyadicLedger' sealRow cert' ->
                RegularCauchyLimitModulusPacket input modulus precision threshold' window'
                  readback dyadicLedger' sealRow provenance cert' bundle pkg ∧
                  hsame window window' ∧ hsame dyadicLedger dyadicLedger' ∧
                    hsame cert cert' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameThreshold inputModulusThreshold' thresholdPrecisionWindow'
    windowReadbackLedger' ledgerSealCert'
  obtain ⟨inputUnary, modulusUnary, precisionUnary, sealUnary, provenanceUnary,
    inputModulusThreshold, thresholdPrecisionWindow, windowReadbackLedger, ledgerSealCert,
    provenancePkg⟩ := packet
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameThreshold (hsame_refl precision) thresholdPrecisionWindow
      thresholdPrecisionWindow'
  have sameLedger : hsame dyadicLedger dyadicLedger' :=
    cont_respects_hsame sameWindow (hsame_refl readback) windowReadbackLedger
      windowReadbackLedger'
  have sameCert : hsame cert cert' :=
    cont_respects_hsame sameLedger (hsame_refl sealRow) ledgerSealCert ledgerSealCert'
  have transported :
      RegularCauchyLimitModulusPacket input modulus precision threshold' window' readback
        dyadicLedger' sealRow provenance cert' bundle pkg := by
    exact ⟨inputUnary, modulusUnary, precisionUnary, sealUnary, provenanceUnary,
      inputModulusThreshold', thresholdPrecisionWindow', windowReadbackLedger',
      ledgerSealCert', provenancePkg⟩
  exact ⟨transported, sameWindow, sameLedger, sameCert⟩

end BEDC.Derived.RegularCauchyLimitModulusUp
