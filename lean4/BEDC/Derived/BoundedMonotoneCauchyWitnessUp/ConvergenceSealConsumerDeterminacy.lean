import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_consumer_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      consumerRead normalRead decisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule consumerRead →
        Cont consumerRead witness normalRead →
          Cont normalRead sealRow decisionRead →
            PkgSig bundle decisionRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory sealRow ∧ UnaryHistory consumerRead ∧ UnaryHistory normalRead ∧
                  UnaryHistory decisionRead ∧ Cont source schedule consumerRead ∧
                    Cont consumerRead witness normalRead ∧
                      Cont normalRead sealRow decisionRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle decisionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleConsumer consumerWitnessNormal normalSealDecision decisionPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleConsumer
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed consumerUnary witnessUnary consumerWitnessNormal
  have decisionUnary : UnaryHistory decisionRead :=
    unary_cont_closed normalUnary sealUnary normalSealDecision
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, sealUnary, consumerUnary, normalUnary,
      decisionUnary, sourceScheduleConsumer, consumerWitnessNormal, normalSealDecision,
      provenancePkg, decisionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
