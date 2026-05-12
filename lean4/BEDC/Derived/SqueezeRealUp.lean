import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SqueezeRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SqueezeRealCarrier [AskSetup] [PackageSetup]
    (lower middle upper tolerance lowerLedger upperLedger sealRow transportRow provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory middle ∧ UnaryHistory upper ∧
    UnaryHistory tolerance ∧ UnaryHistory lowerLedger ∧ UnaryHistory upperLedger ∧
      UnaryHistory sealRow ∧ UnaryHistory transportRow ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont lower middle lowerLedger ∧
          Cont middle upper upperLedger ∧ Cont tolerance lowerLedger upperLedger ∧
            Cont upperLedger sealRow transportRow ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameCert pkg

theorem SqueezeRealCarrier_sandwich_exactness [AskSetup] [PackageSetup]
    {lower middle upper tolerance lowerLedger upperLedger sealRow transportRow provenance
      nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SqueezeRealCarrier lower middle upper tolerance lowerLedger upperLedger sealRow transportRow
        provenance nameCert bundle pkg ->
      Cont tolerance lowerLedger upperLedger ->
        Cont upperLedger sealRow consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory tolerance ∧ UnaryHistory lowerLedger ∧ UnaryHistory upperLedger ∧
              UnaryHistory sealRow ∧ UnaryHistory consumer ∧
                Cont tolerance lowerLedger upperLedger ∧ Cont upperLedger sealRow consumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  intro carrier toleranceLowerUpper upperSealConsumer consumerPkg
  obtain ⟨_lowerUnary, _middleUnary, _upperUnary, toleranceUnary, lowerLedgerUnary,
    upperLedgerUnary, sealUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _lowerMiddleLedger, _middleUpperLedger, _carrierToleranceLowerUpper,
    _carrierUpperSealTransport, provenancePkg, _nameCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed upperLedgerUnary sealUnary upperSealConsumer
  exact
    ⟨toleranceUnary, lowerLedgerUnary, upperLedgerUnary, sealUnary, consumerUnary,
      toleranceLowerUpper, upperSealConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.SqueezeRealUp
