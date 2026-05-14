import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_source_totality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead criterionTail limitRead monotoneRead sealExhaustRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow provenance convergenceRead →
      Cont regular witness criterionTail →
      Cont criterionTail sealRow convergenceRead →
      Cont sealRow provenance limitRead →
      Cont source schedule monotoneRead →
      Cont monotoneRead trap sealExhaustRead →
      PkgSig bundle convergenceRead pkg →
      PkgSig bundle limitRead pkg →
      PkgSig bundle sealExhaustRead pkg →
        UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
          UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
            UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory convergenceRead ∧
              UnaryHistory criterionTail ∧ UnaryHistory limitRead ∧ UnaryHistory monotoneRead ∧
                UnaryHistory sealExhaustRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle convergenceRead pkg ∧ PkgSig bundle limitRead pkg ∧
                    PkgSig bundle sealExhaustRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier sealProvenanceConvergence regularWitnessCriterion criterionSealConvergence
    sealProvenanceLimit sourceScheduleMonotone monotoneTrapExhaust convergencePkg limitPkg
    sealExhaustPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have criterionUnary : UnaryHistory criterionTail :=
    unary_cont_closed regularUnary witnessUnary regularWitnessCriterion
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceLimit
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleMonotone
  have sealExhaustUnary : UnaryHistory sealExhaustRead :=
    unary_cont_closed monotoneUnary trapUnary monotoneTrapExhaust
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, convergenceUnary, criterionUnary, limitUnary, monotoneUnary,
      sealExhaustUnary, provenancePkg, convergencePkg, limitPkg, sealExhaustPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
