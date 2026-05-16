import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_seal_factorization_triad [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      monotoneRead criterionRead observationRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule monotoneRead →
        Cont monotoneRead witness criterionRead →
          Cont criterionRead ledger observationRead →
            Cont observationRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                  UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory monotoneRead ∧
                    UnaryHistory criterionRead ∧ UnaryHistory observationRead ∧
                      UnaryHistory sealRead ∧ Cont source schedule monotoneRead ∧
                        Cont monotoneRead witness criterionRead ∧
                          Cont criterionRead ledger observationRead ∧
                            Cont observationRead sealRow sealRead ∧
                              Cont source schedule regular ∧ Cont regular witness trap ∧
                                Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleMonotone monotoneWitnessCriterion criterionLedgerObservation
    observationSealRead sealReadPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleMonotone
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed monotoneUnary witnessUnary monotoneWitnessCriterion
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed criterionUnary ledgerUnary criterionLedgerObservation
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed observationUnary sealUnary observationSealRead
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, sealUnary, monotoneUnary,
      criterionUnary, observationUnary, sealReadUnary, sourceScheduleMonotone,
      monotoneWitnessCriterion, criterionLedgerObservation, observationSealRead,
      sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
