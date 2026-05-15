import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_nonescape [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead readbackRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule sourceRead ->
        Cont sourceRead regular readbackRead ->
          Cont readbackRead sealRow completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory completionRead ∧
                      Cont source schedule sourceRead ∧ Cont sourceRead regular readbackRead ∧
                        Cont readbackRead sealRow completionRead ∧
                          Cont source schedule regular ∧ Cont regular witness trap ∧
                            Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead readbackRoute completionRoute completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed sourceReadUnary regularUnary readbackRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed readbackUnary sealUnary completionRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      sourceReadUnary, readbackUnary, completionUnary, sourceScheduleRead, readbackRoute,
      completionRoute, sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg,
      completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
