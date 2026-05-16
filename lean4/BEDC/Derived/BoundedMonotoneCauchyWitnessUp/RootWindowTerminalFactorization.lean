import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_window_terminal_factorization
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootWindow tailLedger sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule rootWindow ->
        Cont rootWindow witness tailLedger ->
          Cont tailLedger sealRow sealRead ->
            Cont sealRead provenance completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory rootWindow ∧ UnaryHistory tailLedger ∧ UnaryHistory sealRead ∧
                  UnaryHistory completionRead ∧ Cont source schedule rootWindow ∧
                    Cont rootWindow witness tailLedger ∧ Cont tailLedger sealRow sealRead ∧
                      Cont sealRead provenance completionRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRoot rootWitnessTail tailSealRead sealCompletion completionPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootWindow :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRoot
  have tailUnary : UnaryHistory tailLedger :=
    unary_cont_closed rootUnary witnessUnary rootWitnessTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealUnary tailSealRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealCompletion
  exact
    ⟨rootUnary, tailUnary, sealReadUnary, completionUnary, sourceScheduleRoot,
      rootWitnessTail, tailSealRead, sealCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
