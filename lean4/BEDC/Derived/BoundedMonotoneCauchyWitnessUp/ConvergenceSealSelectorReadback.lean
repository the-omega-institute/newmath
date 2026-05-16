import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_selector_readback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      selectorRead criterionRead convergenceRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule selectorRead →
        Cont selectorRead witness criterionRead →
          Cont criterionRead sealRow convergenceRead →
            Cont convergenceRead provenance terminalRead →
              PkgSig bundle terminalRead pkg →
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                  UnaryHistory selectorRead ∧ UnaryHistory criterionRead ∧
                    UnaryHistory convergenceRead ∧ UnaryHistory terminalRead ∧
                      Cont source schedule selectorRead ∧
                        Cont selectorRead witness criterionRead ∧
                          Cont criterionRead sealRow convergenceRead ∧
                            Cont convergenceRead provenance terminalRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleSelector selectorWitnessCriterion criterionSealConvergence
    convergenceProvenanceTerminal terminalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSelector
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed selectorUnary witnessUnary selectorWitnessCriterion
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealConvergence
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed convergenceUnary provenanceUnary convergenceProvenanceTerminal
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, selectorUnary, criterionUnary, convergenceUnary,
      terminalUnary, sourceScheduleSelector, selectorWitnessCriterion, criterionSealConvergence,
      convergenceProvenanceTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
