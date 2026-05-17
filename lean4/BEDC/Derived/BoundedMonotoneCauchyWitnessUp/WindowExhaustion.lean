import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_exhaustion [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead modulusRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness modulusRead →
          Cont modulusRead ledger budgetRead →
            PkgSig bundle budgetRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory ledger ∧ UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory budgetRead ∧ Cont source schedule windowRead ∧
                    Cont windowRead witness modulusRead ∧ Cont modulusRead ledger budgetRead ∧
                      Cont source schedule regular ∧ Cont regular witness trap ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessModulus modulusLedgerBudget budgetPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessModulus
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed modulusUnary ledgerUnary modulusLedgerBudget
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, windowUnary, modulusUnary,
      budgetUnary, sourceScheduleWindow, windowWitnessModulus, modulusLedgerBudget,
      sourceScheduleRegular, regularWitnessTrap, provenancePkg, budgetPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
