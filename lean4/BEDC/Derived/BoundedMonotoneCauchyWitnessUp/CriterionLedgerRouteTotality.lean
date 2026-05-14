import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_criterion_ledger_route_totality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      criterionRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule criterionRead →
        Cont criterionRead ledger ledgerRead →
          Cont ledgerRead sealRow publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory source ∧ UnaryHistory ledger ∧ UnaryHistory criterionRead ∧
                UnaryHistory ledgerRead ∧ UnaryHistory publicRead ∧
                  Cont source schedule criterionRead ∧
                    Cont criterionRead ledger ledgerRead ∧
                      Cont ledgerRead sealRow publicRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleCriterion criterionLedgerRead ledgerSealPublic publicPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleCriterion
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed criterionUnary ledgerUnary criterionLedgerRead
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerReadUnary sealUnary ledgerSealPublic
  exact
    ⟨sourceUnary, ledgerUnary, criterionUnary, ledgerReadUnary, publicUnary,
      sourceScheduleCriterion, criterionLedgerRead, ledgerSealPublic, provenancePkg,
      publicPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
