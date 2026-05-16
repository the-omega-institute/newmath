import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_window_convergence_seal_lock
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule rootRead ->
        Cont rootRead sealRow convergenceRead ->
          PkgSig bundle convergenceRead pkg ->
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory sealRow ∧
              UnaryHistory rootRead ∧ UnaryHistory convergenceRead ∧
                Cont source schedule rootRead ∧ Cont rootRead sealRow convergenceRead ∧
                  Cont source schedule regular ∧ Cont regular witness trap ∧
                    Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier sourceScheduleRoot rootSealConvergence convergencePkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary,
    _trapUnary, sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
    trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRoot
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed rootUnary sealUnary rootSealConvergence
  exact
    ⟨sourceUnary, scheduleUnary, sealUnary, rootUnary, convergenceUnary, sourceScheduleRoot,
      rootSealConvergence, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      provenancePkg, convergencePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
