import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_monotone_bound_route [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      boundRead windowRead tailRead trapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source ledger boundRead →
        Cont boundRead schedule windowRead →
          Cont windowRead witness tailRead →
            Cont tailRead trap trapRead →
              PkgSig bundle trapRead pkg →
                UnaryHistory source ∧ UnaryHistory ledger ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory trap ∧ UnaryHistory boundRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory tailRead ∧ UnaryHistory trapRead ∧
                      Cont source ledger boundRead ∧ Cont boundRead schedule windowRead ∧
                        Cont windowRead witness tailRead ∧ Cont tailRead trap trapRead ∧
                          Cont source schedule regular ∧ Cont regular witness trap ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle trapRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceLedgerBound boundScheduleWindow windowWitnessTail tailTrapRead trapReadPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed sourceUnary ledgerUnary sourceLedgerBound
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed boundUnary scheduleUnary boundScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessTail
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed tailUnary trapUnary tailTrapRead
  exact
    ⟨sourceUnary, ledgerUnary, scheduleUnary, witnessUnary, trapUnary, boundUnary, windowUnary,
      tailUnary, trapReadUnary, sourceLedgerBound, boundScheduleWindow, windowWitnessTail,
      tailTrapRead, sourceScheduleRegular, regularWitnessTrap, provenancePkg, trapReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
