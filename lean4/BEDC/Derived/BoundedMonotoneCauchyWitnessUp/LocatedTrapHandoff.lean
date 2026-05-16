import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_located_trap_handoff
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert tailRead trapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead ledger trapRead →
          PkgSig bundle trapRead pkg →
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
              UnaryHistory trap ∧ UnaryHistory tailRead ∧ UnaryHistory trapRead ∧
                Cont source schedule tailRead ∧ Cont tailRead ledger trapRead ∧
                  Cont regular witness trap ∧ Cont trap sealRow route ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle trapRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailLedgerTrap trapPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, regularWitnessTrap,
    trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed tailUnary ledgerUnary tailLedgerTrap
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, trapUnary, tailUnary, trapReadUnary,
      sourceScheduleTail, tailLedgerTrap, regularWitnessTrap, trapSealRoute, provenancePkg,
      trapPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
