import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_route_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead criterionRead convergenceRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead witness criterionRead →
          Cont criterionRead sealRow convergenceRead →
            Cont convergenceRead provenance sealRead →
              Cont sealRead localCert publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory envelopeRead ∧ UnaryHistory criterionRead ∧
                    UnaryHistory convergenceRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory publicRead ∧ Cont source schedule envelopeRead ∧
                        Cont envelopeRead witness criterionRead ∧
                          Cont criterionRead sealRow convergenceRead ∧
                            Cont convergenceRead provenance sealRead ∧
                              Cont sealRead localCert publicRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleEnvelope envelopeWitnessCriterion criterionSealConvergence
    convergenceProvenanceSeal sealLocalPublic publicPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalCertRoute routeUnary).right
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed envelopeUnary witnessUnary envelopeWitnessCriterion
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealConvergence
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed convergenceUnary provenanceUnary convergenceProvenanceSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary localCertUnary sealLocalPublic
  exact
    ⟨envelopeUnary, criterionUnary, convergenceUnary, sealReadUnary, publicUnary,
      sourceScheduleEnvelope, envelopeWitnessCriterion, criterionSealConvergence,
      convergenceProvenanceSeal, sealLocalPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
