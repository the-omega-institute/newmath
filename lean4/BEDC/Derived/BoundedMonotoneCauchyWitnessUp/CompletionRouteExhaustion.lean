import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_completion_route_exhaustion [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead completionRead sealInput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular finiteRead →
          Cont finiteRead sealRow completionRead →
            Cont completionRead provenance sealInput →
              PkgSig bundle sealInput pkg →
                UnaryHistory envelopeRead ∧ UnaryHistory finiteRead ∧
                  UnaryHistory completionRead ∧ UnaryHistory sealInput ∧
                    Cont source schedule envelopeRead ∧
                      Cont envelopeRead regular finiteRead ∧
                        Cont finiteRead sealRow completionRead ∧
                          Cont completionRead provenance sealInput ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle sealInput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute finiteRoute completionRoute sealInputRoute sealInputPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary finiteRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed finiteUnary sealUnary completionRoute
  have sealInputUnary : UnaryHistory sealInput :=
    unary_cont_closed completionUnary provenanceUnary sealInputRoute
  exact
    ⟨envelopeUnary, finiteUnary, completionUnary, sealInputUnary, envelopeRoute, finiteRoute,
      completionRoute, sealInputRoute, provenancePkg, sealInputPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_envelope_uniqueness [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeA finiteA completionA sealInputA envelopeB finiteB completionB sealInputB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeA →
        Cont envelopeA regular finiteA →
          Cont finiteA sealRow completionA →
            Cont completionA provenance sealInputA →
              Cont source schedule envelopeB →
                Cont envelopeB regular finiteB →
                  Cont finiteB sealRow completionB →
                    Cont completionB provenance sealInputB →
                      PkgSig bundle sealInputA pkg →
                        PkgSig bundle sealInputB pkg →
                          UnaryHistory envelopeA ∧ UnaryHistory envelopeB ∧
                            hsame envelopeA (append source schedule) ∧
                              hsame envelopeB (append source schedule) ∧
                                PkgSig bundle sealInputA pkg ∧
                                  PkgSig bundle sealInputB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier envelopeRouteA finiteRouteA completionRouteA sealInputRouteA
    envelopeRouteB finiteRouteB completionRouteB sealInputRouteB sealInputPkgA sealInputPkgB
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have envelopeUnaryA : UnaryHistory envelopeA :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRouteA
  have envelopeUnaryB : UnaryHistory envelopeB :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRouteB
  have sameEnvelopeA : hsame envelopeA (append source schedule) := by
    cases envelopeRouteA
    rfl
  have sameEnvelopeB : hsame envelopeB (append source schedule) := by
    cases envelopeRouteB
    rfl
  exact
    ⟨envelopeUnaryA, envelopeUnaryB, sameEnvelopeA, sameEnvelopeB, sealInputPkgA,
      sealInputPkgB⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
