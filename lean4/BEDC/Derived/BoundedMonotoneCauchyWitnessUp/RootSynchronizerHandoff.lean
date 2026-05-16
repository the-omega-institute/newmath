import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_synchronizer_handoff
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead synchronizerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source regular rootRead ->
        Cont rootRead route synchronizerRead ->
          PkgSig bundle synchronizerRead pkg ->
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory route ∧ UnaryHistory rootRead ∧
                  UnaryHistory synchronizerRead ∧ Cont source regular rootRead ∧
                    Cont rootRead route synchronizerRead ∧ Cont source schedule regular ∧
                      Cont regular witness trap ∧ Cont trap sealRow route ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle synchronizerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceRegularRoot rootRouteSynchronizer synchronizerPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed rootUnary routeUnary rootRouteSynchronizer
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, routeUnary, rootUnary, synchronizerUnary, sourceRegularRoot,
      rootRouteSynchronizer, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      provenancePkg, synchronizerPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
