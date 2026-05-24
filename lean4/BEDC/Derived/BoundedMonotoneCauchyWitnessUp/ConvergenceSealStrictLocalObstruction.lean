import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_strict_local_obstruction
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      finiteTail selectorRead criterionRead convergenceRead terminalRead obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule finiteTail →
        Cont finiteTail witness selectorRead →
          Cont selectorRead ledger criterionRead →
            Cont criterionRead sealRow convergenceRead →
              Cont convergenceRead provenance terminalRead →
                hsame obstruction terminalRead →
                  PkgSig bundle terminalRead pkg →
                    UnaryHistory obstruction ∧ Cont source schedule finiteTail ∧
                      Cont finiteTail witness selectorRead ∧
                        Cont selectorRead ledger criterionRead ∧
                          Cont criterionRead sealRow convergenceRead ∧
                            Cont convergenceRead provenance terminalRead ∧
                              PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleFinite finiteWitnessSelector selectorLedgerCriterion
    criterionSealConvergence convergenceProvenanceTerminal sameObstruction terminalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have finiteTailUnary : UnaryHistory finiteTail :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleFinite
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed finiteTailUnary witnessUnary finiteWitnessSelector
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed selectorUnary ledgerUnary selectorLedgerCriterion
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealConvergence
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed convergenceUnary provenanceUnary convergenceProvenanceTerminal
  exact
    ⟨unary_transport_symm terminalUnary sameObstruction, sourceScheduleFinite,
      finiteWitnessSelector, selectorLedgerCriterion, criterionSealConvergence,
      convergenceProvenanceTerminal, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
