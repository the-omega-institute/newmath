import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_route_naturality
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead criterionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular criterionRead →
          Cont criterionRead sealRow realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory envelopeRead ∧
                    UnaryHistory criterionRead ∧ UnaryHistory realRead ∧
                      Cont source schedule envelopeRead ∧
                        Cont envelopeRead regular criterionRead ∧
                          Cont criterionRead sealRow realRead ∧
                            Cont source schedule regular ∧ Cont regular witness trap ∧
                              Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute criterionRoute realRoute realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed envelopeUnary regularUnary criterionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed criterionUnary sealUnary realRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      envelopeUnary, criterionUnary, realUnary, envelopeRoute, criterionRoute, realRoute,
      sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
