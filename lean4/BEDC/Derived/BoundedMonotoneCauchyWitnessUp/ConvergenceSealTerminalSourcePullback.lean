import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_terminal_source_pullback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead trapRead sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead witness trapRead →
          Cont trapRead sealRow sealRead →
            Cont sealRead provenance terminalRead →
              PkgSig bundle terminalRead pkg →
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                  UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory provenance ∧
                    UnaryHistory sourceRead ∧ UnaryHistory trapRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory terminalRead ∧
                        Cont source schedule sourceRead ∧
                          Cont sourceRead witness trapRead ∧
                            Cont trapRead sealRow sealRead ∧
                              Cont sealRead provenance terminalRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceScheduleSourceRead sourceReadWitnessTrapRead trapReadSealRowSealRead
    sealReadProvenanceTerminalRead terminalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSourceRead
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed sourceReadUnary witnessUnary sourceReadWitnessTrapRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapReadSealRowSealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealReadProvenanceTerminalRead
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, trapUnary, sealUnary, provenanceUnary,
      sourceReadUnary, trapReadUnary, sealReadUnary, terminalReadUnary,
      sourceScheduleSourceRead, sourceReadWitnessTrapRead, trapReadSealRowSealRead,
      sealReadProvenanceTerminalRead, provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
