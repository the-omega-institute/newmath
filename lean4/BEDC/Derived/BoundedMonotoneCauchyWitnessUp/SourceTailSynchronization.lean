import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_source_tail_synchronization [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead tailRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead regular tailRead →
          Cont tailRead ledger budgetRead →
            PkgSig bundle budgetRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory ledger ∧ UnaryHistory sourceRead ∧ UnaryHistory tailRead ∧
                  UnaryHistory budgetRead ∧ Cont source schedule sourceRead ∧
                    Cont sourceRead regular tailRead ∧ Cont tailRead ledger budgetRead ∧
                      Cont source schedule regular ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead sourceReadRegularTail tailLedgerBudget budgetPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceReadUnary regularUnary sourceReadRegularTail
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailReadUnary ledgerUnary tailLedgerBudget
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, ledgerUnary, sourceReadUnary, tailReadUnary,
      budgetReadUnary, sourceScheduleRead, sourceReadRegularTail, tailLedgerBudget,
      sourceScheduleRegular, provenancePkg, budgetPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
