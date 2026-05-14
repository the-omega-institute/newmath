import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_source_row_exhaustion [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule sourceRead ->
        Cont sourceRead regular handoffRead ->
          PkgSig bundle handoffRead pkg ->
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory sourceRead ∧ UnaryHistory handoffRead ∧
                Cont source schedule sourceRead ∧ Cont sourceRead regular handoffRead ∧
                  Cont source schedule regular ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleSourceRead sourceReadRegular handoffPkg
  rcases carrier with
    ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
      _sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap,
      _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSourceRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed sourceReadUnary regularUnary sourceReadRegular
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, sourceReadUnary, handoffReadUnary,
      sourceScheduleSourceRead, sourceReadRegular, sourceScheduleRegular, provenancePkg,
      handoffPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
