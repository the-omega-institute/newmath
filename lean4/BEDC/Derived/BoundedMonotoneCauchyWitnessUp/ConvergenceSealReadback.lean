import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_readback [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead scheduleRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead regular scheduleRead →
          Cont scheduleRead witness regularRead →
            Cont regularRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory regular ∧
                  UnaryHistory witness ∧ UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧
                    UnaryHistory scheduleRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory sealRead ∧ Cont source schedule sourceRead ∧
                        Cont sourceRead regular scheduleRead ∧
                          Cont scheduleRead witness regularRead ∧
                            Cont regularRead sealRow sealRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead sourceReadRegularSchedule scheduleReadWitnessRegular
    regularReadSealRowSeal sealReadPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
      carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed sourceReadUnary regularUnary sourceReadRegularSchedule
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleReadUnary witnessUnary scheduleReadWitnessRegular
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary sealUnary regularReadSealRowSeal
  exact
    ⟨sourceUnary, scheduleUnary, regularUnary, witnessUnary, sealUnary, sourceReadUnary,
      scheduleReadUnary, regularReadUnary, sealReadUnary, sourceScheduleRead,
      sourceReadRegularSchedule, scheduleReadWitnessRegular, regularReadSealRowSeal,
      provenancePkg, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
