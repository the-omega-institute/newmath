import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_completion_envelope_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeA envelopeB finiteA finiteB trapA trapB sealA sealB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeA →
        Cont source schedule envelopeB →
          hsame envelopeA envelopeB →
            Cont envelopeA regular finiteA →
              Cont envelopeB regular finiteB →
                Cont finiteA trap trapA →
                  Cont finiteB trap trapB →
                    Cont trapA sealRow sealA →
                      Cont trapB sealRow sealB →
                        hsame finiteA finiteB ∧ hsame trapA trapB ∧ hsame sealA sealB ∧
                          UnaryHistory envelopeA ∧ UnaryHistory envelopeB ∧
                            UnaryHistory finiteA ∧ UnaryHistory finiteB ∧ UnaryHistory trapA ∧
                              UnaryHistory trapB ∧ UnaryHistory sealA ∧
                                UnaryHistory sealB := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleEnvelopeA sourceScheduleEnvelopeB sameEnvelope
    envelopeRegularFiniteA envelopeRegularFiniteB finiteTrapA finiteTrapB trapSealA trapSealB
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have envelopeUnaryA : UnaryHistory envelopeA :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelopeA
  have envelopeUnaryB : UnaryHistory envelopeB :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelopeB
  have finiteUnaryA : UnaryHistory finiteA :=
    unary_cont_closed envelopeUnaryA regularUnary envelopeRegularFiniteA
  have finiteUnaryB : UnaryHistory finiteB :=
    unary_cont_closed envelopeUnaryB regularUnary envelopeRegularFiniteB
  have trapUnaryA : UnaryHistory trapA :=
    unary_cont_closed finiteUnaryA trapUnary finiteTrapA
  have trapUnaryB : UnaryHistory trapB :=
    unary_cont_closed finiteUnaryB trapUnary finiteTrapB
  have sealUnaryA : UnaryHistory sealA :=
    unary_cont_closed trapUnaryA sealUnary trapSealA
  have sealUnaryB : UnaryHistory sealB :=
    unary_cont_closed trapUnaryB sealUnary trapSealB
  have sameFinite : hsame finiteA finiteB :=
    cont_respects_hsame sameEnvelope (hsame_refl regular) envelopeRegularFiniteA
      envelopeRegularFiniteB
  have sameTrap : hsame trapA trapB :=
    cont_respects_hsame sameFinite (hsame_refl trap) finiteTrapA finiteTrapB
  have sameSeal : hsame sealA sealB :=
    cont_respects_hsame sameTrap (hsame_refl sealRow) trapSealA trapSealB
  exact
    ⟨sameFinite, sameTrap, sameSeal, envelopeUnaryA, envelopeUnaryB, finiteUnaryA,
      finiteUnaryB, trapUnaryA, trapUnaryB, sealUnaryA, sealUnaryB⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
