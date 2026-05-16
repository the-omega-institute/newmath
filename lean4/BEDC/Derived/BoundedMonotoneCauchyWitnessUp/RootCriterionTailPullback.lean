import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_criterion_tail_pullback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead budgetRead pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule envelopeRead ->
        Cont envelopeRead ledger budgetRead ->
          Cont budgetRead trap pullbackRead ->
            PkgSig bundle pullbackRead pkg ->
              UnaryHistory source /\ UnaryHistory schedule /\ UnaryHistory ledger /\
                UnaryHistory trap /\ UnaryHistory envelopeRead /\ UnaryHistory budgetRead /\
                  UnaryHistory pullbackRead /\ Cont source schedule envelopeRead /\
                    Cont envelopeRead ledger budgetRead /\ Cont budgetRead trap pullbackRead /\
                      Cont source schedule regular /\ Cont regular witness trap /\
                        Cont trap sealRow route /\ PkgSig bundle provenance pkg /\
                          PkgSig bundle pullbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute budgetRoute pullbackRoute pullbackPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed envelopeUnary ledgerUnary budgetRoute
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed budgetUnary trapUnary pullbackRoute
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, trapUnary, envelopeUnary, budgetUnary,
      pullbackUnary, envelopeRoute, budgetRoute, pullbackRoute, sourceScheduleRegular,
      regularWitnessTrap, trapSealRoute, provenancePkg, pullbackPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
