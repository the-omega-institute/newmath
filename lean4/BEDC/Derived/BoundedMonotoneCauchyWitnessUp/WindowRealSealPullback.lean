import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_real_seal_pullback [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead tailRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule windowRead ->
        Cont windowRead ledger tailRead ->
          Cont tailRead sealRow realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory windowRead ∧
                  UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                    Cont source schedule windowRead ∧ Cont windowRead ledger tailRead ∧
                      Cont tailRead sealRow realRead ∧ Cont source schedule regular ∧
                        Cont regular witness trap ∧ Cont trap sealRow route ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowLedgerTail tailSealReal realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerTail
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealUnary tailSealReal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, ledgerUnary, sealUnary, windowUnary,
      tailUnary, realUnary, sourceScheduleWindow, windowLedgerTail, tailSealReal,
      sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
