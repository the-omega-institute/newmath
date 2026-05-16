import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_completion_terminality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead criterionRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead witness criterionRead →
          Cont criterionRead sealRow completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory sealRow ∧ UnaryHistory tailRead ∧ UnaryHistory criterionRead ∧
                  UnaryHistory completionRead ∧ Cont source schedule tailRead ∧
                    Cont tailRead witness criterionRead ∧
                      Cont criterionRead sealRow completionRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailWitnessCriterion criterionSealCompletion completionPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessCriterion
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealCompletion
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, sealUnary, tailUnary, criterionUnary,
      completionUnary, sourceScheduleTail, tailWitnessCriterion, criterionSealCompletion,
      provenancePkg, completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
