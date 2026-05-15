import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_seal_route_minimality [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead modulusRead budgetRead trapRead sealRead completionRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness modulusRead →
          Cont modulusRead ledger budgetRead →
            Cont budgetRead trap trapRead →
              Cont trapRead sealRow sealRead →
                Cont sealRead provenance completionRead →
                  Cont completionRead localCert finalRead →
                    PkgSig bundle finalRead pkg →
                      UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                        UnaryHistory ledger ∧ UnaryHistory trap ∧ UnaryHistory sealRow ∧
                          UnaryHistory localCert ∧ UnaryHistory windowRead ∧
                            UnaryHistory modulusRead ∧ UnaryHistory budgetRead ∧
                              UnaryHistory trapRead ∧ UnaryHistory sealRead ∧
                                UnaryHistory completionRead ∧ UnaryHistory finalRead ∧
                                  Cont source schedule windowRead ∧
                                    Cont windowRead witness modulusRead ∧
                                      Cont modulusRead ledger budgetRead ∧
                                        Cont budgetRead trap trapRead ∧
                                          Cont trapRead sealRow sealRead ∧
                                            Cont sealRead provenance completionRead ∧
                                              Cont completionRead localCert finalRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessModulus modulusLedgerBudget budgetTrapRead
    trapSealRead sealProvenanceCompletion completionLocalFinal finalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).right
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessModulus
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed modulusUnary ledgerUnary modulusLedgerBudget
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed budgetUnary trapUnary budgetTrapRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealProvenanceCompletion
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed completionUnary localCertUnary completionLocalFinal
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      localCertUnary, windowUnary, modulusUnary, budgetUnary, trapReadUnary,
      sealReadUnary, completionUnary, finalUnary, sourceScheduleWindow, windowWitnessModulus,
      modulusLedgerBudget, budgetTrapRead, trapSealRead, sealProvenanceCompletion,
      completionLocalFinal, provenancePkg, finalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
