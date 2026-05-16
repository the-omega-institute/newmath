import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_located_trap_convergence_seal_cofinality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootWindow trapRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source regular rootWindow ->
        Cont rootWindow trap trapRead ->
          Cont trapRead sealRow terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory rootWindow ∧ UnaryHistory trapRead ∧
                    UnaryHistory terminalRead ∧ Cont source schedule regular ∧
                      Cont regular witness trap ∧ Cont source regular rootWindow ∧
                        Cont rootWindow trap trapRead ∧
                          Cont trapRead sealRow terminalRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularRoot rootWindowTrapRead trapReadSealTerminal terminalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed rootWindowUnary trapUnary rootWindowTrapRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed trapReadUnary sealUnary trapReadSealTerminal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      rootWindowUnary, trapReadUnary, terminalReadUnary, sourceScheduleRegular,
      regularWitnessTrap, sourceRegularRoot, rootWindowTrapRead, trapReadSealTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
