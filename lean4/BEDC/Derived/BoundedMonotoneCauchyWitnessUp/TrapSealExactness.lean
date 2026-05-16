import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_trap_seal_exactness [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      budgetRead trapRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont ledger trap budgetRead →
        Cont budgetRead trap trapRead →
          Cont trapRead sealRow sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory trapRead ∧
                UnaryHistory sealRead ∧ Cont budgetRead trap trapRead ∧
                  Cont trapRead sealRow sealRead ∧ Cont trap sealRow route ∧
                    Cont route provenance sealRow ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier ledgerTrapBudget budgetTrapRead trapSealRead sealReadPkg
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed ledgerUnary trapUnary ledgerTrapBudget
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed budgetUnary trapUnary budgetTrapRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealRead
  exact
    ⟨trapUnary, sealUnary, trapReadUnary, sealReadUnary, budgetTrapRead, trapSealRead,
      trapSealRoute, routeProvenanceSeal, provenancePkg, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
