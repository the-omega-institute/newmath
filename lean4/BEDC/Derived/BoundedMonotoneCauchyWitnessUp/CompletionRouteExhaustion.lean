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

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
