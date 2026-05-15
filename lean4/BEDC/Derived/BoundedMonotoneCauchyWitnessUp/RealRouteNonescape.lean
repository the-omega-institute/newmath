import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_route_nonescape [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead budgetRead trapRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead ledger budgetRead →
          Cont budgetRead trap trapRead →
            Cont trapRead sealRow realRead →
              PkgSig bundle realRead pkg →
                UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                    UnaryHistory sealRow ∧ UnaryHistory windowRead ∧
                      UnaryHistory budgetRead ∧ UnaryHistory trapRead ∧
                        UnaryHistory realRead ∧ Cont source schedule regular ∧
                          Cont source schedule windowRead ∧
                            Cont windowRead ledger budgetRead ∧
                              Cont budgetRead trap trapRead ∧
                                Cont trapRead sealRow realRead ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowLedgerBudget budgetTrapRead trapSealReal realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerBudget
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed budgetUnary trapUnary budgetTrapRead
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealReal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      windowUnary, budgetUnary, trapReadUnary, realUnary, sourceScheduleRegular,
      sourceScheduleWindow, windowLedgerBudget, budgetTrapRead, trapSealReal, provenancePkg,
      realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
