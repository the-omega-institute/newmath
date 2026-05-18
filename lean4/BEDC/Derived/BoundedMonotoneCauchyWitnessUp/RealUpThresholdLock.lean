import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_realup_threshold_lock [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert grid
      criterion synchronizer observation threshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule grid →
        Cont grid witness criterion →
          Cont criterion trap synchronizer →
            Cont synchronizer sealRow observation →
              Cont observation localCert threshold →
                PkgSig bundle threshold pkg →
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                    UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory grid ∧
                      UnaryHistory criterion ∧ UnaryHistory synchronizer ∧
                        UnaryHistory observation ∧ UnaryHistory threshold ∧
                          Cont source schedule grid ∧ Cont grid witness criterion ∧
                            Cont criterion trap synchronizer ∧
                              Cont synchronizer sealRow observation ∧
                                Cont observation localCert threshold ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle threshold pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier sourceScheduleGrid gridWitnessCriterion criterionTrapSynchronizer
    synchronizerSealObservation observationLocalThreshold thresholdPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).right
  have gridUnary : UnaryHistory grid :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleGrid
  have criterionUnary : UnaryHistory criterion :=
    unary_cont_closed gridUnary witnessUnary gridWitnessCriterion
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed criterionUnary trapUnary criterionTrapSynchronizer
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed synchronizerUnary sealUnary synchronizerSealObservation
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed observationUnary localCertUnary observationLocalThreshold
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, trapUnary, sealUnary, gridUnary,
      criterionUnary, synchronizerUnary, observationUnary, thresholdUnary, sourceScheduleGrid,
      gridWitnessCriterion, criterionTrapSynchronizer, synchronizerSealObservation,
      observationLocalThreshold, provenancePkg, thresholdPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
