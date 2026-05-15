import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_window_extraction [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead modulusRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule windowRead ->
        Cont windowRead witness modulusRead ->
          Cont modulusRead ledger ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory ledger ∧ UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory ledgerRead ∧ Cont source schedule windowRead ∧
                    Cont windowRead witness modulusRead ∧ Cont modulusRead ledger ledgerRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessModulus modulusLedgerRead ledgerReadPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessModulus
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modulusUnary ledgerUnary modulusLedgerRead
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, ledgerUnary, windowUnary, modulusUnary,
      ledgerReadUnary, sourceScheduleWindow, windowWitnessModulus, modulusLedgerRead,
      provenancePkg, ledgerReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
