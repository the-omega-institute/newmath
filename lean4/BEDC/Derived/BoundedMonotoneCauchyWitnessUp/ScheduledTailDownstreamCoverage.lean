import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_scheduled_tail_downstream_coverage
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      toleranceRead finiteRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule toleranceRead ->
        Cont toleranceRead ledger finiteRead ->
          Cont finiteRead sealRow downstreamRead ->
            PkgSig bundle downstreamRead pkg ->
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory finiteRead ∧ UnaryHistory downstreamRead ∧
                      Cont source schedule toleranceRead ∧
                        Cont toleranceRead ledger finiteRead ∧
                          Cont finiteRead sealRow downstreamRead ∧
                            Cont source schedule regular ∧ Cont regular witness trap ∧
                              Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTolerance toleranceLedgerFinite finiteSealDownstream
    downstreamPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTolerance
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed toleranceUnary ledgerUnary toleranceLedgerFinite
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed finiteUnary sealUnary finiteSealDownstream
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      toleranceUnary, finiteUnary, downstreamUnary, sourceScheduleTolerance,
      toleranceLedgerFinite, finiteSealDownstream, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, provenancePkg, downstreamPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
