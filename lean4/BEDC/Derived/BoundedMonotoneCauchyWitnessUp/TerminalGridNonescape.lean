import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_terminal_grid_nonescape
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont ledger trap gridRead ->
        Cont gridRead sealRow terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory gridRead ∧
                  UnaryHistory terminalRead ∧ Cont source schedule regular ∧
                    Cont regular witness trap ∧ Cont ledger trap gridRead ∧
                      Cont gridRead sealRow terminalRead ∧ Cont trap sealRow route ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier ledgerTrapGrid gridSealTerminal terminalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have gridUnary : UnaryHistory gridRead :=
    unary_cont_closed ledgerUnary trapUnary ledgerTrapGrid
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed gridUnary sealUnary gridSealTerminal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, provenanceUnary, gridUnary, terminalUnary, sourceScheduleRegular,
      regularWitnessTrap, ledgerTrapGrid, gridSealTerminal, trapSealRoute, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
