import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_window_strict_obstruction [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead modulusRead ledgerRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness modulusRead →
          Cont modulusRead ledger ledgerRead →
            Cont ledgerRead sealRow realSealRead →
              PkgSig bundle realSealRead pkg →
                UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory realSealRead ∧
                    Cont source schedule windowRead ∧
                      Cont windowRead witness modulusRead ∧
                        Cont modulusRead ledger ledgerRead ∧
                          Cont ledgerRead sealRow realSealRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessModulus modulusLedgerRead ledgerSealRead
    realSealPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowReadUnary witnessUnary windowWitnessModulus
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modulusReadUnary ledgerUnary modulusLedgerRead
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed ledgerReadUnary sealUnary ledgerSealRead
  exact
    ⟨windowReadUnary, modulusReadUnary, ledgerReadUnary, realSealReadUnary,
      sourceScheduleWindow, windowWitnessModulus, modulusLedgerRead, ledgerSealRead,
      provenancePkg, realSealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
