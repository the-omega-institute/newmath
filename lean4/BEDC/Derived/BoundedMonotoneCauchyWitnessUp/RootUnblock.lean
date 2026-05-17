import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_unblock [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead trapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead trap trapRead →
          PkgSig bundle trapRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory envelopeRead ∧ UnaryHistory trapRead ∧
                  Cont source schedule regular ∧ Cont regular witness trap ∧
                    Cont trap sealRow route ∧ Cont source schedule envelopeRead ∧
                      Cont envelopeRead trap trapRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle trapRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleEnvelope envelopeTrapRead trapReadPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed envelopeUnary trapUnary envelopeTrapRead
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      envelopeUnary, trapReadUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      sourceScheduleEnvelope, envelopeTrapRead, provenancePkg, trapReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
