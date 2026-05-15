import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_read_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      source' schedule' witness' sealRow' envelopeRead envelopeRead' criterionRead
      criterionRead' convergenceRead convergenceRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      hsame source source' →
        hsame schedule schedule' →
          hsame witness witness' →
            hsame sealRow sealRow' →
              Cont source schedule envelopeRead →
                Cont source' schedule' envelopeRead' →
                  Cont envelopeRead witness criterionRead →
                    Cont envelopeRead' witness' criterionRead' →
                      Cont criterionRead sealRow convergenceRead →
                        Cont criterionRead' sealRow' convergenceRead' →
                          UnaryHistory envelopeRead ∧ UnaryHistory criterionRead ∧
                            UnaryHistory convergenceRead ∧ hsame envelopeRead envelopeRead' ∧
                              hsame criterionRead criterionRead' ∧
                                hsame convergenceRead convergenceRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceSame scheduleSame witnessSame sealSame sourceScheduleRead
    sourceScheduleRead' envelopeWitnessRead envelopeWitnessRead' criterionSealRead
    criterionSealRead'
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed envelopeUnary witnessUnary envelopeWitnessRead
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealRead
  have envelopeSame : hsame envelopeRead envelopeRead' :=
    cont_respects_hsame sourceSame scheduleSame sourceScheduleRead sourceScheduleRead'
  have criterionSame : hsame criterionRead criterionRead' :=
    cont_respects_hsame envelopeSame witnessSame envelopeWitnessRead envelopeWitnessRead'
  have convergenceSame : hsame convergenceRead convergenceRead' :=
    cont_respects_hsame criterionSame sealSame criterionSealRead criterionSealRead'
  exact
    ⟨envelopeUnary, criterionUnary, convergenceUnary, envelopeSame, criterionSame,
      convergenceSame⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
