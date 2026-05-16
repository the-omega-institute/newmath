import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_budget_seal_correspondence
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      budgetRead sealThreshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont schedule witness budgetRead →
        Cont budgetRead trap sealThreshold →
          PkgSig bundle sealThreshold pkg →
            UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
              UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory budgetRead ∧
                UnaryHistory sealThreshold ∧ Cont schedule witness budgetRead ∧
                  Cont budgetRead trap sealThreshold ∧ Cont trap sealRow route ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sealThreshold pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier scheduleWitnessBudget budgetTrapSeal sealThresholdPkg
  obtain ⟨_sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessBudget
  have sealThresholdUnary : UnaryHistory sealThreshold :=
    unary_cont_closed budgetUnary trapUnary budgetTrapSeal
  exact
    ⟨scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary, budgetUnary,
      sealThresholdUnary, scheduleWitnessBudget, budgetTrapSeal, trapSealRoute,
      provenancePkg, sealThresholdPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
