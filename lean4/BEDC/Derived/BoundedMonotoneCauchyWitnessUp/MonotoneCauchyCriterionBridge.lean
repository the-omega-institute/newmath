import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_monotone_cauchy_criterion_bridge
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      monotoneTail criterionPacket criterionLedger publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule monotoneTail →
        Cont monotoneTail witness criterionPacket →
          Cont criterionPacket ledger criterionLedger →
            Cont criterionLedger sealRow publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                  UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory monotoneTail ∧
                    UnaryHistory criterionPacket ∧ UnaryHistory criterionLedger ∧
                      UnaryHistory publicRead ∧ Cont source schedule monotoneTail ∧
                        Cont monotoneTail witness criterionPacket ∧
                          Cont criterionPacket ledger criterionLedger ∧
                            Cont criterionLedger sealRow publicRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailWitnessCriterion criterionLedgerRoute
    ledgerSealPublic publicReadPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have monotoneTailUnary : UnaryHistory monotoneTail :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have criterionPacketUnary : UnaryHistory criterionPacket :=
    unary_cont_closed monotoneTailUnary witnessUnary tailWitnessCriterion
  have criterionLedgerUnary : UnaryHistory criterionLedger :=
    unary_cont_closed criterionPacketUnary ledgerUnary criterionLedgerRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed criterionLedgerUnary sealUnary ledgerSealPublic
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, sealUnary, monotoneTailUnary,
      criterionPacketUnary, criterionLedgerUnary, publicReadUnary, sourceScheduleTail,
      tailWitnessCriterion, criterionLedgerRoute, ledgerSealPublic, provenancePkg,
      publicReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
