import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead tailRead trapRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness tailRead →
          Cont tailRead ledger trapRead →
            Cont trapRead sealRow realRead →
              PkgSig bundle realRead pkg →
                UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                    UnaryHistory sealRow ∧ UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory trapRead ∧ UnaryHistory realRead ∧
                        Cont source schedule regular ∧ Cont regular witness trap ∧
                          Cont trap sealRow route ∧ Cont source schedule windowRead ∧
                            Cont windowRead witness tailRead ∧ Cont tailRead ledger trapRead ∧
                              Cont trapRead sealRow realRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessTail tailLedgerTrap trapSealReal realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessTail
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerTrap
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealReal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      windowUnary, tailUnary, trapReadUnary, realUnary, sourceScheduleRegular,
      regularWitnessTrap, trapSealRoute, sourceScheduleWindow, windowWitnessTail, tailLedgerTrap,
      trapSealReal, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
