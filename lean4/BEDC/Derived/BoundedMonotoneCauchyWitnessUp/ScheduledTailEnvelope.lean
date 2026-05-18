import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedMonotoneCauchyWitnessScheduledTailEnvelope [AskSetup] [PackageSetup]
    (source regular schedule witness ledger trap transport route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
    UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont source schedule regular ∧ Cont regular witness trap ∧
          Cont transport localCert route ∧ PkgSig bundle provenance pkg

theorem BoundedMonotoneCauchyWitnessScheduledTailEnvelope_admission [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      BoundedMonotoneCauchyWitnessScheduledTailEnvelope source regular schedule witness ledger
        trap transport route provenance localCert bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  rcases carrier with
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, sourceScheduleRegular, regularWitnessTrap, _trapSealRoute,
      transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_left_factor routeProvenanceSeal sealUnary
  have transportUnary : UnaryHistory transport :=
    unary_cont_left_factor transportLocalCertRoute routeUnary
  have localCertUnary : UnaryHistory localCert :=
    unary_cont_right_factor transportLocalCertRoute routeUnary
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      transportUnary, routeUnary, provenanceUnary, localCertUnary, sourceScheduleRegular,
      regularWitnessTrap, transportLocalCertRoute, provenancePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
