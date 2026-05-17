import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_cofinal_grid_readback_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail gridStream gridRegSeq gridReal gridTransport
      gridReplay gridProvenance gridName readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridBudget →
        UnaryHistory gridClassifier →
          UnaryHistory gridStream →
            UnaryHistory gridRegSeq →
              UnaryHistory gridReal →
                Cont sealRow gridBudget gridLedger →
                  Cont gridLedger gridClassifier gridTail →
                    Cont gridTail gridStream gridTransport →
                      Cont gridTransport gridRegSeq gridReplay →
                        Cont gridReplay gridReal readback →
                          PkgSig bundle readback pkg →
                            UnaryHistory sealRow ∧ UnaryHistory gridLedger ∧
                              UnaryHistory gridTail ∧ UnaryHistory gridTransport ∧
                                UnaryHistory gridReplay ∧ UnaryHistory readback ∧
                                  Cont sealRow gridBudget gridLedger ∧
                                    Cont gridLedger gridClassifier gridTail ∧
                                      Cont gridTail gridStream gridTransport ∧
                                        Cont gridTransport gridRegSeq gridReplay ∧
                                          Cont gridReplay gridReal readback ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridClassifierUnary gridStreamUnary gridRegSeqUnary gridRealUnary
    sealGridBudget gridLedgerClassifier gridTailStream gridTransportRegSeq gridReplayReal
    readbackPkg
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed sealUnary gridBudgetUnary sealGridBudget
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridLedgerUnary gridClassifierUnary gridLedgerClassifier
  have gridTransportUnary : UnaryHistory gridTransport :=
    unary_cont_closed gridTailUnary gridStreamUnary gridTailStream
  have gridReplayUnary : UnaryHistory gridReplay :=
    unary_cont_closed gridTransportUnary gridRegSeqUnary gridTransportRegSeq
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed gridReplayUnary gridRealUnary gridReplayReal
  exact
    ⟨sealUnary, gridLedgerUnary, gridTailUnary, gridTransportUnary, gridReplayUnary,
      readbackUnary, sealGridBudget, gridLedgerClassifier, gridTailStream, gridTransportRegSeq,
      gridReplayReal, provenancePkg, readbackPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
