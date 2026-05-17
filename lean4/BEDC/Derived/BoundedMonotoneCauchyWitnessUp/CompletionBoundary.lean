import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_completion_boundary [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead trapRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular finiteRead →
          Cont finiteRead trap trapRead →
            Cont trapRead sealRow completionRead →
              PkgSig bundle completionRead pkg →
                UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                    UnaryHistory sealRow ∧ UnaryHistory envelopeRead ∧
                      UnaryHistory finiteRead ∧ UnaryHistory trapRead ∧
                        UnaryHistory completionRead ∧ Cont source schedule envelopeRead ∧
                          Cont envelopeRead regular finiteRead ∧ Cont finiteRead trap trapRead ∧
                            Cont trapRead sealRow completionRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont
  intro carrier sourceScheduleEnvelope envelopeRegularFinite finiteTrapRead trapReadSealCompletion
    completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary envelopeRegularFinite
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed finiteUnary trapUnary finiteTrapRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed trapReadUnary sealUnary trapReadSealCompletion
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      envelopeUnary, finiteUnary, trapReadUnary, completionUnary, sourceScheduleEnvelope,
      envelopeRegularFinite, finiteTrapRead, trapReadSealCompletion, provenancePkg,
      completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
