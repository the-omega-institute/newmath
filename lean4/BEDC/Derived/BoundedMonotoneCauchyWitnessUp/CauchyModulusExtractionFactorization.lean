import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_cauchy_modulus_extraction_factorization
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      modulusRead thresholdRead extractionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont schedule witness modulusRead ->
        Cont modulusRead ledger thresholdRead ->
          Cont thresholdRead sealRow extractionRead ->
            PkgSig bundle extractionRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory modulusRead ∧
                  UnaryHistory thresholdRead ∧ UnaryHistory extractionRead ∧
                    Cont source schedule regular ∧ Cont regular witness trap ∧
                      Cont schedule witness modulusRead ∧
                        Cont modulusRead ledger thresholdRead ∧
                          Cont thresholdRead sealRow extractionRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle extractionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleWitnessModulus modulusLedgerThreshold thresholdSealExtraction
    extractionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessModulus
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed modulusUnary ledgerUnary modulusLedgerThreshold
  have extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed thresholdUnary sealUnary thresholdSealExtraction
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, modulusUnary,
      thresholdUnary, extractionUnary, sourceScheduleRegular, regularWitnessTrap,
      scheduleWitnessModulus, modulusLedgerThreshold, thresholdSealExtraction, provenancePkg,
      extractionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
