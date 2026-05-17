import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_l10_terminal_route_refusal_completeness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead trapRead sealRead terminalRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead witness trapRead →
          Cont trapRead sealRow sealRead →
            Cont sealRead route terminalRead →
              Cont terminalRead provenance consumerRead →
                PkgSig bundle terminalRead pkg →
                  PkgSig bundle consumerRead pkg →
                    UnaryHistory source ∧ UnaryHistory sourceRead ∧
                      UnaryHistory trapRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory terminalRead ∧ UnaryHistory consumerRead ∧
                          Cont source schedule sourceRead ∧
                            Cont sourceRead witness trapRead ∧
                              Cont trapRead sealRow sealRead ∧
                                Cont sealRead route terminalRead ∧
                                  Cont terminalRead provenance consumerRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle terminalRead pkg ∧
                                        PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceScheduleSourceRead sourceReadWitnessTrapRead trapReadSealRowSealRead
    sealReadRouteTerminalRead terminalReadProvenanceConsumerRead terminalPkg consumerPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSourceRead
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed sourceReadUnary witnessUnary sourceReadWitnessTrapRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapReadSealRowSealRead
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary routeUnary sealReadRouteTerminalRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed terminalReadUnary provenanceUnary terminalReadProvenanceConsumerRead
  exact
    ⟨sourceUnary, sourceReadUnary, trapReadUnary, sealReadUnary, terminalReadUnary,
      consumerReadUnary, sourceScheduleSourceRead, sourceReadWitnessTrapRead,
      trapReadSealRowSealRead, sealReadRouteTerminalRead, terminalReadProvenanceConsumerRead,
      provenancePkg, terminalPkg, consumerPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
