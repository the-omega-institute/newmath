import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_completion_observation_route [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead trapRead sealRead observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular finiteRead →
          Cont finiteRead trap trapRead →
            Cont trapRead sealRow sealRead →
              Cont sealRead provenance observationRead →
                PkgSig bundle observationRead pkg →
                  UnaryHistory envelopeRead ∧ UnaryHistory finiteRead ∧
                    UnaryHistory trapRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory observationRead ∧ Cont source schedule envelopeRead ∧
                        Cont envelopeRead regular finiteRead ∧ Cont finiteRead trap trapRead ∧
                          Cont trapRead sealRow sealRead ∧
                            Cont sealRead provenance observationRead ∧
                              Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle observationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleEnvelope envelopeRegularFinite finiteTrapRead trapSealRead
    sealProvenanceObservation observationPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary envelopeRegularFinite
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed finiteUnary trapUnary finiteTrapRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealRead
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealProvenanceObservation
  exact
    ⟨envelopeUnary, finiteUnary, trapReadUnary, sealReadUnary, observationUnary,
      sourceScheduleEnvelope, envelopeRegularFinite, finiteTrapRead, trapSealRead,
      sealProvenanceObservation, trapSealRoute, provenancePkg, observationPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
