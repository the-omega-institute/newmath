import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_l10_exit_consumer_package [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont trap sealRow route →
        Cont route provenance exitRead →
          PkgSig bundle exitRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory route ∧ UnaryHistory exitRead ∧
                  Cont source schedule regular ∧ Cont regular witness trap ∧
                    Cont trap sealRow route ∧ Cont route provenance exitRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle exitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier trapSealRoute routeProvenanceExit exitPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
    _carrierTrapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceExit
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, routeUnary, exitUnary, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, routeProvenanceExit, provenancePkg, exitPkg⟩
