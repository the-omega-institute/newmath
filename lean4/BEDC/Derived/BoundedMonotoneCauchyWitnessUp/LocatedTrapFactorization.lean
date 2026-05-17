import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_located_trap_factorization
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead trapRead sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule tailRead ->
        Cont tailRead ledger trapRead ->
          Cont trapRead sealRow sealRead ->
            Cont sealRead route terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                  UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory route ∧
                    UnaryHistory tailRead ∧ UnaryHistory trapRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory terminal ∧
                        Cont source schedule tailRead ∧ Cont tailRead ledger trapRead ∧
                          Cont trapRead sealRow sealRead ∧ Cont sealRead route terminal ∧
                            Cont regular witness trap ∧ Cont trap sealRow route ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier sourceScheduleTail tailLedgerTrap trapSealRead sealTerminal terminalPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerTrap
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealRead
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealReadUnary routeUnary sealTerminal
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, trapUnary, sealUnary, routeUnary, tailUnary,
      trapReadUnary, sealReadUnary, terminalUnary, sourceScheduleTail, tailLedgerTrap,
      trapSealRead, sealTerminal, regularWitnessTrap, trapSealRoute, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
