import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_seal_trap_budget_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailA tailB budgetA budgetB trapA trapB sealA sealB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailA →
        Cont source schedule tailB →
          hsame tailA tailB →
            Cont tailA ledger budgetA →
              Cont tailB ledger budgetB →
                Cont budgetA trap trapA →
                  Cont budgetB trap trapB →
                    Cont trapA sealRow sealA →
                      Cont trapB sealRow sealB →
                        hsame budgetA budgetB ∧ hsame trapA trapB ∧ hsame sealA sealB ∧
                          UnaryHistory tailA ∧ UnaryHistory tailB ∧ UnaryHistory budgetA ∧
                            UnaryHistory budgetB ∧ UnaryHistory trapA ∧ UnaryHistory trapB ∧
                              UnaryHistory sealA ∧ UnaryHistory sealB := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleTailA sourceScheduleTailB sameTail tailLedgerBudgetA
    tailLedgerBudgetB budgetTrapA budgetTrapB trapSealA trapSealB
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have tailUnaryA : UnaryHistory tailA :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTailA
  have tailUnaryB : UnaryHistory tailB :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTailB
  have budgetUnaryA : UnaryHistory budgetA :=
    unary_cont_closed tailUnaryA ledgerUnary tailLedgerBudgetA
  have budgetUnaryB : UnaryHistory budgetB :=
    unary_cont_closed tailUnaryB ledgerUnary tailLedgerBudgetB
  have trapUnaryA : UnaryHistory trapA :=
    unary_cont_closed budgetUnaryA trapUnary budgetTrapA
  have trapUnaryB : UnaryHistory trapB :=
    unary_cont_closed budgetUnaryB trapUnary budgetTrapB
  have sealUnaryA : UnaryHistory sealA :=
    unary_cont_closed trapUnaryA sealUnary trapSealA
  have sealUnaryB : UnaryHistory sealB :=
    unary_cont_closed trapUnaryB sealUnary trapSealB
  have sameBudget : hsame budgetA budgetB :=
    cont_respects_hsame sameTail (hsame_refl ledger) tailLedgerBudgetA tailLedgerBudgetB
  have sameTrap : hsame trapA trapB :=
    cont_respects_hsame sameBudget (hsame_refl trap) budgetTrapA budgetTrapB
  have sameSeal : hsame sealA sealB :=
    cont_respects_hsame sameTrap (hsame_refl sealRow) trapSealA trapSealB
  exact
    ⟨sameBudget, sameTrap, sameSeal, tailUnaryA, tailUnaryB, budgetUnaryA, budgetUnaryB,
      trapUnaryA, trapUnaryB, sealUnaryA, sealUnaryB⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
