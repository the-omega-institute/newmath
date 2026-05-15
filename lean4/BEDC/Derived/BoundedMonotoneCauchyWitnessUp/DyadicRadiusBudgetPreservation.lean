import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_dyadic_radius_budget_preservation [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead budgetRead radiusRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead ledger budgetRead →
          Cont budgetRead witness radiusRead →
            Cont radiusRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory source ∧ UnaryHistory ledger ∧ UnaryHistory witness ∧
                  UnaryHistory sealRow ∧ UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                    UnaryHistory radiusRead ∧ UnaryHistory sealRead ∧
                      Cont source schedule tailRead ∧ Cont tailRead ledger budgetRead ∧
                        Cont budgetRead witness radiusRead ∧
                          Cont radiusRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailLedgerBudget budgetWitnessRadius radiusSealRead
    sealReadPkg
  rcases carrier with
    ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
      sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
      _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerBudget
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed budgetUnary witnessUnary budgetWitnessRadius
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed radiusUnary sealUnary radiusSealRead
  exact
    ⟨sourceUnary, ledgerUnary, witnessUnary, sealUnary, tailUnary, budgetUnary, radiusUnary,
      sealReadUnary, sourceScheduleTail, tailLedgerBudget, budgetWitnessRadius,
      radiusSealRead, provenancePkg, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
