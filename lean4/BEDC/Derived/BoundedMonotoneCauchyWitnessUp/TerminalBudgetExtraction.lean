import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_terminal_budget_extraction [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail uniformIndex uniformWindow uniformModulus
      uniformTail uniformSeal diagonalBudget terminalRead rootRead gridRead uniformRead
      diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridBudget →
        UnaryHistory gridLedger →
          UnaryHistory gridClassifier →
            UnaryHistory gridTail →
              UnaryHistory uniformIndex →
                UnaryHistory uniformWindow →
                  UnaryHistory uniformModulus →
                    UnaryHistory uniformTail →
                      UnaryHistory uniformSeal →
                        UnaryHistory diagonalBudget →
                          Cont source regular rootRead →
                            Cont rootRead gridBudget gridRead →
                              Cont gridRead gridLedger uniformRead →
                                Cont uniformRead uniformIndex diagonalRead →
                                  Cont diagonalRead diagonalBudget terminalRead →
                                    PkgSig bundle terminalRead pkg →
                                      UnaryHistory rootRead ∧ UnaryHistory gridRead ∧
                                        UnaryHistory uniformRead ∧ UnaryHistory diagonalRead ∧
                                          UnaryHistory terminalRead ∧
                                            Cont source regular rootRead ∧
                                              Cont rootRead gridBudget gridRead ∧
                                                Cont gridRead gridLedger uniformRead ∧
                                                  Cont uniformRead uniformIndex diagonalRead ∧
                                                    Cont diagonalRead diagonalBudget terminalRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridLedgerUnary _gridClassifierUnary _gridTailUnary
    uniformIndexUnary _uniformWindowUnary _uniformModulusUnary _uniformTailUnary _uniformSealUnary
    diagonalBudgetUnary sourceRegularRoot rootGridBudget gridLedgerUniform uniformIndexDiagonal
    diagonalTerminal terminalPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have gridReadUnary : UnaryHistory gridRead :=
    unary_cont_closed rootUnary gridBudgetUnary rootGridBudget
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed gridReadUnary gridLedgerUnary gridLedgerUniform
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed uniformReadUnary uniformIndexUnary uniformIndexDiagonal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed diagonalReadUnary diagonalBudgetUnary diagonalTerminal
  exact
    ⟨rootUnary, gridReadUnary, uniformReadUnary, diagonalReadUnary, terminalReadUnary,
      sourceRegularRoot, rootGridBudget, gridLedgerUniform, uniformIndexDiagonal,
      diagonalTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
