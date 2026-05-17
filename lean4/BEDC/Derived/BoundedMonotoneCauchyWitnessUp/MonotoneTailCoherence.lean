import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_monotone_tail_coherence
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      monotoneRead criterionRead modulusRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule monotoneRead ->
        Cont monotoneRead witness criterionRead ->
          Cont schedule ledger modulusRead ->
            Cont criterionRead modulusRead tailRead ->
              PkgSig bundle tailRead pkg ->
                UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory monotoneRead ∧
                    UnaryHistory criterionRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory tailRead ∧ Cont source schedule monotoneRead ∧
                        Cont monotoneRead witness criterionRead ∧
                          Cont schedule ledger modulusRead ∧
                            Cont criterionRead modulusRead tailRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleMonotone monotoneWitnessCriterion scheduleLedgerModulus
    criterionModulusTail tailPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleMonotone
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed monotoneUnary witnessUnary monotoneWitnessCriterion
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerModulus
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed criterionUnary modulusUnary criterionModulusTail
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, monotoneUnary,
      criterionUnary, modulusUnary, tailUnary, sourceScheduleMonotone,
      monotoneWitnessCriterion, scheduleLedgerModulus, criterionModulusTail, provenancePkg,
      tailPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
