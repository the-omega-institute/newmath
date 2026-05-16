import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_socket_separation [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rangeRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source ledger rangeRead →
        Cont schedule witness tailRead →
          PkgSig bundle route pkg →
            UnaryHistory rangeRead ∧ UnaryHistory tailRead ∧ UnaryHistory route ∧
              Cont source ledger rangeRead ∧ Cont schedule witness tailRead ∧
                Cont trap sealRow route ∧ Cont source schedule regular ∧
                  Cont regular witness trap ∧ Cont route provenance sealRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceLedgerRange scheduleWitnessTail routePkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have rangeUnary : UnaryHistory rangeRead :=
    unary_cont_closed sourceUnary ledgerUnary sourceLedgerRange
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessTail
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  exact
    ⟨rangeUnary, tailUnary, routeUnary, sourceLedgerRange, scheduleWitnessTail,
      trapSealRoute, sourceScheduleRegular, regularWitnessTrap, routeProvenanceSeal,
      provenancePkg, routePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
