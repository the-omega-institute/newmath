import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_envelope_strict_local_obstruction
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead observationRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule envelopeRead ->
        Cont envelopeRead ledger observationRead ->
          Cont observationRead sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory envelopeRead ∧ UnaryHistory observationRead ∧
                UnaryHistory sealRead ∧ Cont source schedule envelopeRead ∧
                  Cont envelopeRead ledger observationRead ∧
                    Cont observationRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier sourceScheduleEnvelope envelopeLedgerObservation observationSealRead sealPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed envelopeUnary ledgerUnary envelopeLedgerObservation
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed observationUnary sealUnary observationSealRead
  exact
    ⟨envelopeUnary, observationUnary, sealReadUnary, sourceScheduleEnvelope,
      envelopeLedgerObservation, observationSealRead, provenancePkg, sealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
