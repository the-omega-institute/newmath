import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_seal_route_universal_property [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      leftWindow leftCriterion leftBudget leftTrap leftSeal leftCompletion leftFinal rightWindow
      rightCriterion rightBudget rightTrap rightSeal rightCompletion rightFinal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule leftWindow →
        Cont leftWindow witness leftCriterion →
          Cont leftCriterion ledger leftBudget →
            Cont leftBudget trap leftTrap →
              Cont leftTrap sealRow leftSeal →
                Cont leftSeal provenance leftCompletion →
                  Cont leftCompletion localCert leftFinal →
                    PkgSig bundle leftFinal pkg →
                      Cont source schedule rightWindow →
                        Cont rightWindow witness rightCriterion →
                          Cont rightCriterion ledger rightBudget →
                            Cont rightBudget trap rightTrap →
                              Cont rightTrap sealRow rightSeal →
                                Cont rightSeal provenance rightCompletion →
                                  Cont rightCompletion localCert rightFinal →
                                    PkgSig bundle rightFinal pkg →
                                      UnaryHistory source ∧ UnaryHistory schedule ∧
                                        UnaryHistory witness ∧ UnaryHistory ledger ∧
                                          UnaryHistory trap ∧ UnaryHistory sealRow ∧
                                            UnaryHistory localCert ∧ UnaryHistory leftFinal ∧
                                              UnaryHistory rightFinal ∧
                                                Cont source schedule regular ∧
                                                  Cont regular witness trap ∧
                                                    Cont trap sealRow route ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle leftFinal pkg ∧
                                                          PkgSig bundle rightFinal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleLeft leftWitnessCriterion criterionLedgerBudget budgetTrapLeft
    leftTrapSeal leftSealProvenance leftCompletionLocal leftPkg sourceScheduleRight
    rightWitnessCriterion criterionLedgerRight rightBudgetTrap rightTrapSeal rightSealProvenance
    rightCompletionLocal rightPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).right
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleLeft
  have leftCriterionUnary : UnaryHistory leftCriterion :=
    unary_cont_closed leftWindowUnary witnessUnary leftWitnessCriterion
  have leftBudgetUnary : UnaryHistory leftBudget :=
    unary_cont_closed leftCriterionUnary ledgerUnary criterionLedgerBudget
  have leftTrapUnary : UnaryHistory leftTrap :=
    unary_cont_closed leftBudgetUnary trapUnary budgetTrapLeft
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed leftTrapUnary sealUnary leftTrapSeal
  have leftCompletionUnary : UnaryHistory leftCompletion :=
    unary_cont_closed leftSealUnary provenanceUnary leftSealProvenance
  have leftFinalUnary : UnaryHistory leftFinal :=
    unary_cont_closed leftCompletionUnary localCertUnary leftCompletionLocal
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRight
  have rightCriterionUnary : UnaryHistory rightCriterion :=
    unary_cont_closed rightWindowUnary witnessUnary rightWitnessCriterion
  have rightBudgetUnary : UnaryHistory rightBudget :=
    unary_cont_closed rightCriterionUnary ledgerUnary criterionLedgerRight
  have rightTrapUnary : UnaryHistory rightTrap :=
    unary_cont_closed rightBudgetUnary trapUnary rightBudgetTrap
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed rightTrapUnary sealUnary rightTrapSeal
  have rightCompletionUnary : UnaryHistory rightCompletion :=
    unary_cont_closed rightSealUnary provenanceUnary rightSealProvenance
  have rightFinalUnary : UnaryHistory rightFinal :=
    unary_cont_closed rightCompletionUnary localCertUnary rightCompletionLocal
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      localCertUnary, leftFinalUnary, rightFinalUnary, sourceScheduleRegular,
      regularWitnessTrap, trapSealRoute, provenancePkg, leftPkg, rightPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
