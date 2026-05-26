import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_terminal_window_split_exactness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead trapRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule windowRead ->
        Cont windowRead trap trapRead ->
          Cont trapRead sealRow terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory windowRead ∧ UnaryHistory trapRead ∧
                    UnaryHistory terminalRead ∧ Cont source schedule windowRead ∧
                      Cont windowRead trap trapRead ∧ Cont trapRead sealRow terminalRead ∧
                        Cont source schedule regular ∧ Cont regular witness trap ∧
                          Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowTrapRead trapReadTerminal terminalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed windowUnary trapUnary windowTrapRead
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed trapReadUnary sealUnary trapReadTerminal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      windowUnary, trapReadUnary, terminalUnary, sourceScheduleWindow, windowTrapRead,
      trapReadTerminal, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
