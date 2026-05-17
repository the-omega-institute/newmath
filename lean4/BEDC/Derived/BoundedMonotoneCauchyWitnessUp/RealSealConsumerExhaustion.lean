import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridBudget →
        UnaryHistory gridLedger →
          UnaryHistory gridClassifier →
            UnaryHistory gridTail →
              Cont source schedule realRead →
                PkgSig bundle realRead pkg →
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                    UnaryHistory ledger ∧ UnaryHistory trap ∧ UnaryHistory sealRow ∧
                      UnaryHistory realRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier _gridBudgetUnary _gridLedgerUnary _gridClassifierUnary _gridTailUnary
    sourceScheduleReal realPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleReal
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary, realUnary,
      provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
