import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_source_row_scope [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead guardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source ledger sourceRead ->
        Cont sourceRead schedule guardRead ->
          PkgSig bundle guardRead pkg ->
            UnaryHistory source ∧ UnaryHistory ledger ∧ UnaryHistory schedule ∧
              UnaryHistory sourceRead ∧ UnaryHistory guardRead ∧
                Cont source ledger sourceRead ∧ Cont sourceRead schedule guardRead ∧
                  Cont source schedule regular ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle guardRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceLedgerRead sourceReadScheduleGuard guardPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary ledgerUnary sourceLedgerRead
  have guardReadUnary : UnaryHistory guardRead :=
    unary_cont_closed sourceReadUnary scheduleUnary sourceReadScheduleGuard
  exact
    ⟨sourceUnary, ledgerUnary, scheduleUnary, sourceReadUnary, guardReadUnary,
      sourceLedgerRead, sourceReadScheduleGuard, sourceScheduleRegular, provenancePkg, guardPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
