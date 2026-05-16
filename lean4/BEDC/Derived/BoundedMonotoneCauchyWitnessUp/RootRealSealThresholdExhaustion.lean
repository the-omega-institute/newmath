import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessRootRealSealThresholdExhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead trapRead realThreshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead ledger trapRead →
          Cont trapRead sealRow realThreshold →
            PkgSig bundle realThreshold pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                UnaryHistory tailRead ∧ UnaryHistory trapRead ∧ UnaryHistory sealRow ∧
                  UnaryHistory realThreshold ∧ Cont source schedule tailRead ∧
                    Cont tailRead ledger trapRead ∧ Cont trapRead sealRow realThreshold ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realThreshold pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier sourceScheduleTailRead tailReadLedgerTrapRead trapReadSealRowRealThreshold
    realThresholdPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealRowUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTailRead
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed tailReadUnary ledgerUnary tailReadLedgerTrapRead
  have realThresholdUnary : UnaryHistory realThreshold :=
    unary_cont_closed trapReadUnary sealRowUnary trapReadSealRowRealThreshold
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, tailReadUnary, trapReadUnary, sealRowUnary,
      realThresholdUnary, sourceScheduleTailRead, tailReadLedgerTrapRead,
      trapReadSealRowRealThreshold, provenancePkg, realThresholdPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
